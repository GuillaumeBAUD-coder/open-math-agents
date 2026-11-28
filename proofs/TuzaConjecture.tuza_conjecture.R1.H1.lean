import OMAReductions.R_TuzaConjecture_tuza_conjecture_R1

-- Step TuzaConjecture.tuza_conjecture.R1.H1: hypothesis H1 of reduction TuzaConjecture.tuza_conjecture.R1
-- Credit: @nnkostov

/-!
# Tuza's Conjecture for Graphs with Packing Number at Most One

We prove Tuza's conjecture `τ(G) ≤ 2 ν(G)` when `ν(G) ≤ 1`:

* If `G` is triangle-free, then `τ(G) = 0 ≤ 2 ν(G)`.
* Otherwise `ν(G) = 1`, so any two triangles in `G` share an edge (at least two vertices).
  Fixing a triangle `{a, b, c}`, if two of its three edges cover every triangle of `G` we are done.
  Otherwise three witness triangles omit `c`, `a`, `b` respectively, forcing all three to share
  a common fourth vertex `x` so `G` contains a `K₄` on `{a, b, c, x}`, and the two opposite edges
  `s(a, b)` and `s(c, x)` meet every triangle of `G`.
-/

open TuzaConjecture

theorem OMA.solution : OMA.R_TuzaConjecture_tuza_conjecture_R1.H1 := by
  intro V _ G hν
  classical
  by_cases hfree : G.CliqueFree 3
  · rw [triangleCoverNumber_eq_zero G hfree]
    exact Nat.zero_le _
  · simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hfree
    obtain ⟨t₀, ht₀⟩ := hfree
    have hbdd : BddAbove {n : ℕ | ∃ T : Set (Finset V), IsTrianglePacking G T ∧ T.ncard = n} := by
      refine ⟨Fintype.card (Finset V), ?_⟩
      rintro n ⟨T, _, rfl⟩
      calc T.ncard ≤ (Set.univ : Set (Finset V)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ T) Set.finite_univ
        _ = Fintype.card (Finset V) := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    have hν1_ge : 1 ≤ trianglePackingNumber G := by
      refine le_csSup hbdd ⟨{t₀}, ⟨?_, ?_⟩, Set.ncard_singleton t₀⟩
      · intro t ht
        rw [Set.mem_singleton_iff] at ht
        rwa [ht]
      · intro t₁ ht₁ t₂ ht₂ hne
        rw [Set.mem_singleton_iff] at ht₁ ht₂
        exact absurd (ht₁.trans ht₂.symm) hne
    have hν1 : trianglePackingNumber G = 1 := le_antisymm hν hν1_ge
    rw [hν1, mul_one]
    have hshare : ∀ t₁ t₂ : Finset V, G.IsNClique 3 t₁ → G.IsNClique 3 t₂ →
        2 ≤ (t₁ ∩ t₂).card := by
      intro t₁ t₂ ht₁ ht₂
      by_cases heq : t₁ = t₂
      · subst heq
        rw [Finset.inter_self, ht₁.card_eq]
        omega
      · by_contra hlt
        push Not at hlt
        have hnc : ((t₁ : Set V) ∩ (t₂ : Set V)).ncard ≤ 1 := by
          rw [← Finset.coe_inter, Set.ncard_coe_finset]
          omega
        have hpack : IsTrianglePacking G ({t₁, t₂} : Set (Finset V)) := by
          refine ⟨?_, ?_⟩
          · intro t ht
            rcases ht with rfl | rfl <;> assumption
          · intro u hu v hv huv
            rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
            · exact absurd rfl huv
            · exact hnc
            · rw [Set.inter_comm]
              exact hnc
            · exact absurd rfl huv
        have h2 : 2 ≤ trianglePackingNumber G :=
          le_csSup hbdd ⟨{t₁, t₂}, hpack, Set.ncard_pair heq⟩
        omega
    have hcov2 : ∀ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet →
        (∀ t : Finset V, G.IsNClique 3 t → (∀ v ∈ e₁, v ∈ t) ∨ (∀ v ∈ e₂, v ∈ t)) →
        triangleCoverNumber G ≤ 2 := by
      intro e₁ e₂ he₁ he₂ hcover
      let C : Set (Sym2 V) := {e₁, e₂}
      have hC : IsTriangleCover G C := by
        refine ⟨?_, ?_⟩
        · intro e he
          rcases he with rfl | rfl <;> assumption
        · intro t ht
          rcases hcover t ht with h | h
          · exact ⟨e₁, Set.mem_insert e₁ {e₂}, h⟩
          · exact ⟨e₂, Set.mem_insert_of_mem e₁ rfl, h⟩
      have hCcard : C.ncard ≤ 2 :=
        (Set.ncard_insert_le e₁ {e₂}).trans (by rw [Set.ncard_singleton])
      have hle : triangleCoverNumber G ≤ C.ncard := Nat.sInf_le ⟨C, hC, rfl⟩
      exact hle.trans hCcard
    have hedge_mem : ∀ (u w : V) (t : Finset V), u ∈ t → w ∈ t → ∀ v ∈ s(u, w), v ∈ t := by
      intro u w t hu hw v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
    obtain ⟨a, b, c, hab, hac, hbc, ht₀eq⟩ := Finset.card_eq_three.mp ht₀.card_eq
    have ht₀' : G.IsNClique 3 {a, b, c} := ht₀eq ▸ ht₀
    have hab_edge : s(a, b) ∈ G.edgeSet :=
      G.mem_edgeSet.mpr (ht₀'.1 (by simp) (by simp) hab)
    have hbc_edge : s(b, c) ∈ G.edgeSet :=
      G.mem_edgeSet.mpr (ht₀'.1 (by simp) (by simp) hbc)
    have hac_edge : s(a, c) ∈ G.edgeSet :=
      G.mem_edgeSet.mpr (ht₀'.1 (by simp) (by simp) hac)
    have htwo_of_t0 : ∀ t : Finset V, G.IsNClique 3 t →
        (a ∈ t ∧ b ∈ t) ∨ (b ∈ t ∧ c ∈ t) ∨ (a ∈ t ∧ c ∈ t) := by
      intro t ht
      have hcard := hshare t {a, b, c} ht ht₀'
      by_cases ha : a ∈ t <;> by_cases hb : b ∈ t <;> by_cases hc : c ∈ t
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr (Or.inr ⟨ha, hc⟩)
      · exfalso
        have hsub : t ∩ {a, b, c} ⊆ {a} := by
          intro v hv
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
          rcases hv with ⟨hvt, rfl | rfl | rfl⟩
          · rfl
          · exact absurd hvt hb
          · exact absurd hvt hc
        have hle := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton a)
        omega
      · exact Or.inr (Or.inl ⟨hb, hc⟩)
      · exfalso
        have hsub : t ∩ {a, b, c} ⊆ {b} := by
          intro v hv
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
          rcases hv with ⟨hvt, rfl | rfl | rfl⟩
          · exact absurd hvt ha
          · rfl
          · exact absurd hvt hc
        have hle := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton b)
        omega
      · exfalso
        have hsub : t ∩ {a, b, c} ⊆ {c} := by
          intro v hv
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
          rcases hv with ⟨hvt, rfl | rfl | rfl⟩
          · exact absurd hvt ha
          · exact absurd hvt hb
          · rfl
        have hle := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton c)
        omega
      · exfalso
        have hsub : t ∩ {a, b, c} = ∅ := by
          ext v
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
            iff_false, not_and]
          rintro hvt (rfl | rfl | rfl)
          · exact ha hvt
          · exact hb hvt
          · exact hc hvt
        rw [hsub, Finset.card_empty] at hcard
        omega
    by_cases h1 : ∀ t : Finset V, G.IsNClique 3 t → (a ∈ t ∧ b ∈ t) ∨ (b ∈ t ∧ c ∈ t)
    · refine hcov2 s(a, b) s(b, c) hab_edge hbc_edge fun t ht => ?_
      rcases h1 t ht with ⟨ha, hb⟩ | ⟨hb, hc⟩
      · exact Or.inl (hedge_mem a b t ha hb)
      · exact Or.inr (hedge_mem b c t hb hc)
    by_cases h2 : ∀ t : Finset V, G.IsNClique 3 t → (a ∈ t ∧ b ∈ t) ∨ (a ∈ t ∧ c ∈ t)
    · refine hcov2 s(a, b) s(a, c) hab_edge hac_edge fun t ht => ?_
      rcases h2 t ht with ⟨ha, hb⟩ | ⟨ha, hc⟩
      · exact Or.inl (hedge_mem a b t ha hb)
      · exact Or.inr (hedge_mem a c t ha hc)
    by_cases h3 : ∀ t : Finset V, G.IsNClique 3 t → (b ∈ t ∧ c ∈ t) ∨ (a ∈ t ∧ c ∈ t)
    · refine hcov2 s(b, c) s(a, c) hbc_edge hac_edge fun t ht => ?_
      rcases h3 t ht with ⟨hb, hc⟩ | ⟨ha, hc⟩
      · exact Or.inl (hedge_mem b c t hb hc)
      · exact Or.inr (hedge_mem a c t ha hc)
    have hextract : ∀ (u w : V) (t : Finset V), u ≠ w → t.card = 3 → u ∈ t → w ∈ t →
        ∃ z : V, z ≠ u ∧ z ≠ w ∧ t = {u, w, z} := by
      intro u w t huw hcard hu hw
      obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hcard
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
      rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      · exact absurd rfl huw
      · exact ⟨r, hpr.symm, hqr.symm, rfl⟩
      · exact ⟨q, hpq.symm, hqr, by ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · exact ⟨r, hqr.symm, hpr.symm, by ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · exact absurd rfl huw
      · exact ⟨p, hpq, hpr, by ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · exact ⟨q, hqr, hpq.symm, by ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · exact ⟨p, hpr, hpq, by ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · exact absurd rfl huw
    push Not at h1 h2 h3
    obtain ⟨t₁, ht₁, hnot_t1⟩ := h3
    have ht1_ab : a ∈ t₁ ∧ b ∈ t₁ ∧ c ∉ t₁ := by
      rcases htwo_of_t0 t₁ ht₁ with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨ha, hc⟩
      · exact ⟨ha, hb, fun hc => hnot_t1.1 hb hc⟩
      · exact absurd hc (hnot_t1.1 hb)
      · exact absurd hc (hnot_t1.2 ha)
    obtain ⟨x, hxa, hxb, ht1eq⟩ := hextract a b t₁ hab ht₁.card_eq ht1_ab.1 ht1_ab.2.1
    have hxc : x ≠ c := by
      rintro rfl
      exact ht1_ab.2.2 (ht1eq ▸ by simp)
    obtain ⟨t₂, ht₂, hnot_t2⟩ := h2
    have ht2_bc : b ∈ t₂ ∧ c ∈ t₂ ∧ a ∉ t₂ := by
      rcases htwo_of_t0 t₂ ht₂ with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨ha, hc⟩
      · exact absurd hb (hnot_t2.1 ha)
      · exact ⟨hb, hc, fun ha => hnot_t2.1 ha hb⟩
      · exact absurd hc (hnot_t2.2 ha)
    obtain ⟨y, _hyb, _hyc, ht2eq⟩ := hextract b c t₂ hbc ht₂.card_eq ht2_bc.1 ht2_bc.2.1
    have hyx : y = x := by
      by_contra hne
      have hsub : t₁ ∩ t₂ ⊆ {b} := by
        intro v hv
        rw [Finset.mem_inter] at hv
        rcases hv with ⟨h1v, h2v⟩
        rw [ht1eq] at h1v
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1v
        rcases h1v with rfl | rfl | rfl
        · exact absurd h2v ht2_bc.2.2
        · exact Finset.mem_singleton_self _
        · rw [ht2eq] at h2v
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2v
          rcases h2v with h | h | h
          · exact absurd h hxb
          · exact absurd h hxc
          · exact absurd h.symm hne
      have hcard := hshare t₁ t₂ ht₁ ht₂
      have hle := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton b)
      omega
    rw [hyx] at ht2eq
    obtain ⟨t₃, ht₃, hnot_t3⟩ := h1
    have ht3_ac : a ∈ t₃ ∧ c ∈ t₃ ∧ b ∉ t₃ := by
      rcases htwo_of_t0 t₃ ht₃ with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨ha, hc⟩
      · exact absurd hb (hnot_t3.1 ha)
      · exact absurd hc (hnot_t3.2 hb)
      · exact ⟨ha, hc, fun hb => hnot_t3.1 ha hb⟩
    obtain ⟨z, _hza, _hzc, ht3eq⟩ := hextract a c t₃ hac ht₃.card_eq ht3_ac.1 ht3_ac.2.1
    have hzx : z = x := by
      by_contra hne
      have hsub : t₁ ∩ t₃ ⊆ {a} := by
        intro v hv
        rw [Finset.mem_inter] at hv
        rcases hv with ⟨h1v, h3v⟩
        rw [ht1eq] at h1v
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1v
        rcases h1v with rfl | rfl | rfl
        · exact Finset.mem_singleton_self _
        · exact absurd h3v ht3_ac.2.2
        · rw [ht3eq] at h3v
          simp only [Finset.mem_insert, Finset.mem_singleton] at h3v
          rcases h3v with h | h | h
          · exact absurd h hxa
          · exact absurd h hxc
          · exact absurd h.symm hne
      have hcard := hshare t₁ t₃ ht₁ ht₃
      have hle := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton a)
      omega
    rw [hzx] at ht3eq
    have hcx_edge : s(c, x) ∈ G.edgeSet :=
      G.mem_edgeSet.mpr (ht₂.1 ht2_bc.2.1 (ht2eq ▸ by simp) hxc.symm)
    refine hcov2 s(a, b) s(c, x) hab_edge hcx_edge fun t ht => ?_
    by_contra hneither
    push Not at hneither
    have hnot_ab : ¬ (a ∈ t ∧ b ∈ t) := fun ⟨ha, hb⟩ => by
      obtain ⟨v, hv, hvt⟩ := hneither.1
      exact hvt (hedge_mem a b t ha hb v hv)
    have hnot_cx : ¬ (c ∈ t ∧ x ∈ t) := fun ⟨hc, hx⟩ => by
      obtain ⟨v, hv, hvt⟩ := hneither.2
      exact hvt (hedge_mem c x t hc hx v hv)
    rcases htwo_of_t0 t ht with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨ha, hc⟩
    · exact hnot_ab ⟨ha, hb⟩
    · have ha : a ∉ t := fun ha => hnot_ab ⟨ha, hb⟩
      have hx : x ∉ t := fun hx => hnot_cx ⟨hc, hx⟩
      have hsub : t ∩ t₃ ⊆ {c} := by
        intro v hv
        rw [Finset.mem_inter, ht3eq] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
        rcases hv with ⟨hvt, rfl | rfl | rfl⟩
        · exact absurd hvt ha
        · rfl
        · exact absurd hvt hx
      have hcard := hshare t t₃ ht ht₃
      have hle := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton c)
      omega
    · have hb : b ∉ t := fun hb => hnot_ab ⟨ha, hb⟩
      have hx : x ∉ t := fun hx => hnot_cx ⟨hc, hx⟩
      have hsub : t ∩ t₁ ⊆ {a} := by
        intro v hv
        rw [Finset.mem_inter, ht1eq] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
        rcases hv with ⟨hvt, rfl | rfl | rfl⟩
        · rfl
        · exact absurd hvt hb
        · exact absurd hvt hx
      have hcard := hshare t t₁ ht ht₁
      have hle := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton a)
      omega
