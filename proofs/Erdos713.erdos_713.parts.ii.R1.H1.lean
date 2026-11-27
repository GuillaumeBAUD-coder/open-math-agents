import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1

/-!
# Proof of `Erdos713.erdos_713.parts.ii.R1.H1`

If a bipartite graph `G` on `Fin q` with `≥ 2` edges has a vertex `v` of degree `< 2`,
let `J` be the induced subgraph obtained by deleting `v` (on `Fin (q - 1)`).
We prove via greedy deletion of vertices of degree `< q` that for every `n`,
`extremalNumber n G ≤ extremalNumber n J + q * n`, while `extremalNumber n J ≤ extremalNumber n G`
since `J ⊑ G`.
- If `2 ≤ J.edgeFinset.card`, then `extremalNumber n J - extremalNumber n G = O(n)`.
- If `J.edgeFinset.card < 2`, then `J` has exactly `1` edge (plus isolated vertices), so
  `extremalNumber n J = 0` for `n ≥ q`, giving `extremalNumber n G = O(n)`.
-/

-- Credit: @skhakim

open SimpleGraph Finset Filter Asymptotics
open scoped Classical

private lemma exists_copy_retarget_isolated {r n : ℕ} {J : SimpleGraph (Fin r)}
    {H : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (hS : r ≤ S.card)
    (hH : ∀ x y, H.Adj x y → x ∈ S ∧ y ∈ S)
    (hcopy : J ⊑ H) :
    J ⊑ H.induce (S : Set (Fin n)) := by
  obtain ⟨φ⟩ := hcopy
  let A : Finset (Fin r) := Finset.univ.filter (fun i ↦ ∃ j, J.Adj i j)
  have hA_in_S : ∀ i ∈ A, φ i ∈ S := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨j, hij⟩ := hi.2
    exact (hH (φ i) (φ j) (φ.toHom.map_rel hij)).1
  let B : Finset (Fin r) := Finset.univ \ A
  let used : Finset (Fin n) := A.image φ
  have hused_sub : used ⊆ S := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hA_in_S i hi
  have hcard_avail : B.card ≤ (S \ used).card := by
    have hused_card : used.card = A.card :=
      Finset.card_image_of_injective A φ.injective
    have hSdiff : (S \ used).card = S.card - used.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hused_sub]
    have hAB : A.card + B.card = r := by
      have h1 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin r)) A
      rw [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h1
      dsimp [B]
      omega
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard_avail
  let eB : B ≃ T := Fintype.equivOfCardEq (by simp [hTcard])
  have hdisj_T : Disjoint T used :=
    Finset.disjoint_sdiff.symm.mono_left hTsub
  let g : Fin r → S := fun i ↦
    if hi : i ∈ A then ⟨φ i, hA_in_S i hi⟩
    else ⟨(eB ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩).1,
      (hTsub (eB ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩).2 |> Finset.mem_sdiff.mp).1⟩
  have hg_inj : Function.Injective g := by
    intro i₁ i₂ heq
    by_cases h1 : i₁ ∈ A <;> by_cases h2 : i₂ ∈ A
    · simp only [g, h1, h2, ↓reduceDIte, Subtype.mk.injEq] at heq
      exact φ.injective heq
    · simp only [g, h1, h2, ↓reduceDIte, Subtype.mk.injEq] at heq
      exfalso
      have hmem1 : φ i₁ ∈ used := Finset.mem_image.mpr ⟨i₁, h1, rfl⟩
      have hmem2 : φ i₁ ∈ T := heq ▸ (eB ⟨i₂, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i₂, h2⟩⟩).2
      exact Finset.disjoint_left.mp hdisj_T hmem2 hmem1
    · simp only [g, h1, h2, ↓reduceDIte, Subtype.mk.injEq] at heq
      exfalso
      have hmem1 : φ i₂ ∈ used := Finset.mem_image.mpr ⟨i₂, h2, rfl⟩
      have hmem2 : φ i₂ ∈ T := heq.symm ▸ (eB ⟨i₁, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i₁, h1⟩⟩).2
      exact Finset.disjoint_left.mp hdisj_T hmem2 hmem1
    · simp only [g, h1, h2, ↓reduceDIte, Subtype.mk.injEq] at heq
      have heq' : eB ⟨i₁, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i₁, h1⟩⟩ =
          eB ⟨i₂, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i₂, h2⟩⟩ := Subtype.ext heq
      have := eB.injective heq'
      exact congr_arg Subtype.val this
  refine ⟨⟨⟨g, ?_⟩, hg_inj⟩⟩
  intro i j hij
  have hiA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨j, hij⟩⟩
  have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨i, hij.symm⟩⟩
  change H.Adj (g i).1 (g j).1
  simp only [g, hiA, hjA, ↓reduceDIte]
  exact φ.toHom.map_rel hij

private lemma extend_copy_low_deg {q r n : ℕ} {G : SimpleGraph (Fin q)}
    {v : Fin q} (hdeg : G.degree v < 2) (hr_pos : 0 < r)
    (e : {x : Fin q // x ≠ v} ≃ Fin r)
    (hr : r + 1 = q)
    {H : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (hmin : ∀ x ∈ S, q ≤ (S.filter (fun y ↦ H.Adj x y)).card)
    (hcopy : (SimpleGraph.comap (fun i : Fin r ↦ (e.symm i).1) G) ⊑ H.induce (S : Set (Fin n))) :
    G ⊑ H := by
  let J := SimpleGraph.comap (fun i : Fin r ↦ (e.symm i).1) G
  obtain ⟨φ⟩ := hcopy
  let used : Finset (Fin n) := Finset.univ.image (fun i : Fin r ↦ (φ i).1)
  have hused_card : used.card ≤ r :=
    (Finset.card_image_le).trans (by simp)
  have hex_w : ∃ w ∈ S, w ∉ used ∧ ∀ u : Fin q, G.Adj v u →
      ∀ (hu : u ≠ v), H.Adj w (φ (e ⟨u, hu⟩)).1 := by
    by_cases h0 : G.degree v = 0
    · let x0 : Fin n := (φ ⟨0, hr_pos⟩).1
      have hx0S : x0 ∈ S := (φ ⟨0, hr_pos⟩).2
      have hdeg_x0 : q ≤ (S.filter (fun y ↦ H.Adj x0 y)).card := hmin x0 hx0S
      have hS_gt : used.card < S.card := by
        have hsub : S.filter (fun y ↦ H.Adj x0 y) ⊆ S := Finset.filter_subset _ _
        have := Finset.card_le_card hsub
        omega
      obtain ⟨w, hwS, hw_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hS_gt
      refine ⟨w, hwS, hw_not, fun u hvu _ ↦ ?_⟩
      exfalso
      have hmem : u ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v u).mpr hvu
      have hpos : 0 < G.degree v := Finset.card_pos.mpr ⟨u, hmem⟩
      omega
    · have hdeg1 : G.degree v = 1 := by omega
      have hpos : 0 < (G.neighborFinset v).card := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using (by omega : 0 < G.degree v)
      obtain ⟨u₀, hu₀_mem⟩ := Finset.card_pos.mp hpos
      have hvu₀ : G.Adj v u₀ := (SimpleGraph.mem_neighborFinset G v u₀).mp hu₀_mem
      have hu₀_ne : u₀ ≠ v := hvu₀.ne.symm
      have hu₀_uniq : ∀ u, G.Adj v u → u = u₀ := by
        intro u hvu
        have hu_mem : u ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v u).mpr hvu
        have hsing : (G.neighborFinset v).card = 1 := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg1
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hsing
        rw [hz, Finset.mem_singleton] at hu_mem hu₀_mem
        exact hu_mem.trans hu₀_mem.symm
      let x₀ : Fin n := (φ (e ⟨u₀, hu₀_ne⟩)).1
      have hx₀S : x₀ ∈ S := (φ (e ⟨u₀, hu₀_ne⟩)).2
      have hnb_ge : q ≤ (S.filter (fun y ↦ H.Adj x₀ y)).card := hmin x₀ hx₀S
      have hlt : used.card < (S.filter (fun y ↦ H.Adj x₀ y)).card := by omega
      obtain ⟨w, hw_nb, hw_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      rw [Finset.mem_filter] at hw_nb
      refine ⟨w, hw_nb.1, hw_not, fun u hvu hu ↦ ?_⟩
      have hu_eq : u = u₀ := hu₀_uniq u hvu
      subst hu_eq
      exact hw_nb.2.symm
  obtain ⟨w, _, hw_not, hw_adj⟩ := hex_w
  let f : Fin q → Fin n := fun x ↦ if hx : x = v then w else (φ (e ⟨x, hx⟩)).1
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_cases ha : a = v <;> by_cases hb : b = v
    · exact ha.trans hb.symm
    · simp only [f, ha, hb, ↓reduceDIte] at hab
      exfalso
      apply hw_not
      exact Finset.mem_image.mpr ⟨e ⟨b, hb⟩, Finset.mem_univ _, hab.symm⟩
    · simp only [f, ha, hb, ↓reduceDIte] at hab
      exfalso
      apply hw_not
      exact Finset.mem_image.mpr ⟨e ⟨a, ha⟩, Finset.mem_univ _, hab⟩
    · simp only [f, ha, hb, ↓reduceDIte] at hab
      have hsub : φ (e ⟨a, ha⟩) = φ (e ⟨b, hb⟩) := Subtype.ext hab
      have he_eq := e.injective (φ.injective hsub)
      exact congr_arg Subtype.val he_eq
  refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
  intro a b hab
  by_cases ha : a = v
  · subst ha
    have hb : b ≠ a := hab.ne.symm
    simp only [f, ↓reduceDIte, hb]
    exact hw_adj b hab hb
  · by_cases hb : b = v
    · subst hb
      simp only [f, ha, ↓reduceDIte]
      exact (hw_adj a hab.symm ha).symm
    · simp only [f, ha, hb, ↓reduceDIte]
      have hJadj : J.Adj (e ⟨a, ha⟩) (e ⟨b, hb⟩) := by
        change G.Adj (e.symm (e ⟨a, ha⟩)).1 (e.symm (e ⟨b, hb⟩)).1
        simpa using hab
      exact φ.toHom.map_rel hJadj

private lemma extremalNumber_le_delete_low_deg {q r n : ℕ} {G : SimpleGraph (Fin q)}
    {v : Fin q} (hdeg : G.degree v < 2) (hr_pos : 0 < r)
    (e : {x : Fin q // x ≠ v} ≃ Fin r) (hr : r + 1 = q) :
    extremalNumber n G ≤
      extremalNumber n (SimpleGraph.comap (fun i : Fin r ↦ (e.symm i).1) G) + q * n := by
  let J := SimpleGraph.comap (fun i : Fin r ↦ (e.symm i).1) G
  rw [← Fintype.card_fin n, SimpleGraph.extremalNumber_le_iff]
  intro H _ hGfree
  have hind : ∀ (m : ℕ) (S : Finset (Fin n)), S.card = m →
      #(H.induce (S : Set (Fin n))).edgeFinset ≤ extremalNumber n J + q * m := by
    intro m
    induction m with
    | zero =>
      intro S hS
      have hSe : S = ∅ := Finset.card_eq_zero.mp hS
      subst hSe
      have hempty : (H.induce ((∅ : Finset (Fin n)) : Set (Fin n))).edgeFinset = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rcases e with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        simp at hx
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    | succ k ih =>
      intro S hS
      by_cases hlow : ∃ x ∈ S, (S.filter (fun y ↦ H.Adj x y)).card < q
      · obtain ⟨x, hxS, hdegx⟩ := hlow
        let S' := S.erase x
        have hS'card : S'.card = k := by
          rw [Finset.card_erase_of_mem hxS, hS]; omega
        have hih := ih S' hS'card
        -- Count edges in S as edges in S' plus edges incident to x
        let E_S := (H.induce (S : Set (Fin n))).edgeFinset
        let E_S' := (H.induce (S' : Set (Fin n))).edgeFinset
        have hsplit : E_S.card ≤ E_S'.card + (S.filter (fun y ↦ H.Adj x y)).card := by
          let E_inc := E_S.filter (fun e ↦ (⟨x, hxS⟩ : S) ∈ e)
          let E_rem := E_S.filter (fun e ↦ (⟨x, hxS⟩ : S) ∉ e)
          have hpart : E_S.card = E_inc.card + E_rem.card := by
            exact (Finset.card_filter_add_card_filter_not (s := E_S)
              (p := fun e ↦ (⟨x, hxS⟩ : S) ∈ e)).symm
          have hinc_le : E_inc.card ≤ (S.filter (fun y ↦ H.Adj x y)).card := by
            have hsub : E_inc ⊆ (S.filter (fun y ↦ H.Adj x y)).attach.image
                (fun y ↦ (s(⟨x, hxS⟩, ⟨y.1, (Finset.mem_filter.mp y.2).1⟩) : Sym2 S)) := by
              intro e he
              rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
              rcases e with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
              have hadj : H.Adj a b := he.1
              have hmem_x : (⟨x, hxS⟩ : S) ∈ (s(⟨a, ha⟩, ⟨b, hb⟩) : Sym2 S) := he.2
              simp only [Sym2.mem_iff, Subtype.mk.injEq] at hmem_x
              rw [Finset.mem_image]
              rcases hmem_x with rfl | rfl
              · refine ⟨⟨b, Finset.mem_filter.mpr ⟨hb, hadj⟩⟩, Finset.mem_attach _ _, rfl⟩
              · refine ⟨⟨a, Finset.mem_filter.mpr ⟨ha, hadj.symm⟩⟩, Finset.mem_attach _ _, Sym2.eq_swap⟩
            calc E_inc.card
                ≤ ((S.filter (fun y ↦ H.Adj x y)).attach.image _).card := Finset.card_le_card hsub
              _ ≤ (S.filter (fun y ↦ H.Adj x y)).attach.card := Finset.card_image_le
              _ = (S.filter (fun y ↦ H.Adj x y)).card := Finset.card_attach
          have hrem_le : E_rem.card ≤ E_S'.card := by
            have hsub : E_rem ⊆ E_S'.image (Sym2.map fun a : S' ↦
                (⟨a.1, (Finset.mem_erase.mp a.2).2⟩ : S)) := by
              intro e he
              rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
              rcases e with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
              have hax : a ≠ x := by
                intro h; subst h; exact he.2 (by simp)
              have hbx : b ≠ x := by
                intro h; subst h; exact he.2 (by simp)
              rw [Finset.mem_image]
              refine ⟨s(⟨a, Finset.mem_erase.mpr ⟨hax, ha⟩⟩, ⟨b, Finset.mem_erase.mpr ⟨hbx, hb⟩⟩),
                ?_, rfl⟩
              rw [SimpleGraph.mem_edgeFinset]
              exact he.1
            exact (Finset.card_le_card hsub).trans Finset.card_image_le
          omega
        dsimp only [E_S, E_S'] at hsplit
        have hstep : #(H.induce (S : Set (Fin n))).edgeFinset ≤ extremalNumber n J + q * k + q := by omega
        have hmul : q * (k + 1) = q * k + q := by ring
        omega
      · push Not at hlow
        -- Every x ∈ S has degree ≥ q in H.induce S!
        -- Define H_S on Fin n keeping only edges inside S
        let H_S : SimpleGraph (Fin n) := {
          Adj := fun a b ↦ a ∈ S ∧ b ∈ S ∧ H.Adj a b
          symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.symm⟩⟩
          loopless := ⟨fun _ h ↦ H.ne_of_adj h.2.2 rfl⟩
        }
        have hHS_free : J.Free H_S := by
          intro hcopy
          have hS_ge : q ≤ S.card := by
            have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
            obtain ⟨x0, hx0⟩ := hSne
            have hdeg0 := hlow x0 hx0
            exact hdeg0.trans (Finset.card_le_card (Finset.filter_subset _ _))
          have hcopy_ind : J ⊑ H_S.induce (S : Set (Fin n)) :=
            exists_copy_retarget_isolated (by omega) (fun _ _ h ↦ ⟨h.1, h.2.1⟩) hcopy
          have hcopy_H : J ⊑ H.induce (S : Set (Fin n)) := by
            obtain ⟨φ⟩ := hcopy_ind
            exact ⟨⟨⟨φ, fun hab ↦ (φ.toHom.map_rel hab).2.2⟩, φ.injective⟩⟩
          exact hGfree (extend_copy_low_deg hdeg hr_pos e hr
            (fun x hx ↦ (hlow x hx).trans_eq (congr_arg Finset.card (by ext y; simp))) hcopy_H)
        have hedge_eq : #(H.induce (S : Set (Fin n))).edgeFinset = #H_S.edgeFinset := by
          refine Finset.card_bij (fun e _ ↦ Sym2.map Subtype.val e) ?_ ?_ ?_
          · intro e he
            rw [SimpleGraph.mem_edgeFinset] at he ⊢
            rcases e with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
            exact ⟨ha, hb, he⟩
          · intro e₁ _ e₂ _ heq
            exact Sym2.map.injective Subtype.val_injective heq
          · intro e he
            rw [SimpleGraph.mem_edgeFinset] at he
            rcases e with ⟨a, b⟩
            refine ⟨s(⟨a, he.1⟩, ⟨b, he.2.1⟩), ?_, rfl⟩
            rw [SimpleGraph.mem_edgeFinset]
            exact he.2.2
        have hle_ex : #H_S.edgeFinset ≤ extremalNumber n J := by
          simpa using SimpleGraph.card_edgeFinset_le_extremalNumber hHS_free
        omega
  have htop := hind n Finset.univ (by simp)
  have heq : #(H.induce ((Finset.univ : Finset (Fin n)) : Set (Fin n))).edgeFinset = #H.edgeFinset := by
    refine Finset.card_bij (fun e _ ↦ Sym2.map Subtype.val e) ?_ ?_ ?_
    · intro e he
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      rcases e with ⟨⟨a, _⟩, ⟨b, _⟩⟩
      exact he
    · intro e₁ _ e₂ _ heq
      exact Sym2.map.injective Subtype.val_injective heq
    · intro e he
      rw [SimpleGraph.mem_edgeFinset] at he
      rcases e with ⟨a, b⟩
      exact ⟨s(⟨a, Finset.mem_univ a⟩, ⟨b, Finset.mem_univ b⟩), by simpa using he, rfl⟩
  rw [← heq]
  simpa using htop

private lemma extremalNumber_eq_zero_of_one_edge {r n : ℕ} {J : SimpleGraph (Fin r)}
    (hrn : r ≤ n) (hJ1 : J.edgeFinset.card = 1) :
    extremalNumber n J = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [← Fintype.card_fin n, SimpleGraph.extremalNumber_le_iff]
  intro H _ hJfree
  by_contra hpos
  have hne : H.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨eH, heH⟩ := hne
  rcases eH with ⟨u₁, u₂⟩
  rw [SimpleGraph.mem_edgeFinset] at heH
  have hHadj : H.Adj u₁ u₂ := heH
  have hu_ne : u₁ ≠ u₂ := hHadj.ne
  obtain ⟨eJ, heJ_eq⟩ := Finset.card_eq_one.mp hJ1
  rcases eJ with ⟨i₁, i₂⟩
  have hi_adj : J.Adj i₁ i₂ := by
    have : s(i₁, i₂) ∈ J.edgeFinset := by rw [heJ_eq]; simp
    exact SimpleGraph.mem_edgeFinset.mp this
  have hi_ne : i₁ ≠ i₂ := hi_adj.ne
  have hall_eq : ∀ a b, J.Adj a b → (a = i₁ ∧ b = i₂) ∨ (a = i₂ ∧ b = i₁) := by
    intro a b hab
    have hmem : s(a, b) ∈ J.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hab
    rw [heJ_eq, Finset.mem_singleton, Sym2.eq_iff] at hmem
    exact hmem
  let A : Finset (Fin r) := {i₁, i₂}
  let B : Finset (Fin r) := Finset.univ \ A
  let U : Finset (Fin n) := {u₁, u₂}
  have hB_le : B.card ≤ (Finset.univ \ U).card := by
    have hAcard : A.card = 2 := Finset.card_pair hi_ne
    have hUcard : U.card = 2 := Finset.card_pair hu_ne
    have hBcard : B.card = r - 2 := by
      dsimp [B]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ A),
        Finset.card_univ, Fintype.card_fin, hAcard]
    have hUrem : (Finset.univ \ U).card = n - 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ U),
        Finset.card_univ, Fintype.card_fin, hUcard]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hB_le
  let eB : B ≃ T := Fintype.equivOfCardEq (by simp [hTcard])
  have hdisj_T : Disjoint T U := Finset.disjoint_sdiff.symm.mono_left hTsub
  let f : Fin r → Fin n := fun i ↦
    if h1 : i = i₁ then u₁
    else if h2 : i = i₂ then u₂
    else (eB ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by simp [A, h1, h2]⟩⟩).1
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_cases ha1 : a = i₁
    · by_cases hb1 : b = i₁
      · exact ha1.trans hb1.symm
      · by_cases hb2 : b = i₂
        · simp only [f, ha1, hb2, hi_ne.symm, ↓reduceDIte] at hab; exact absurd hab hu_ne
        · simp only [f, ha1, hb1, hb2, ↓reduceDIte] at hab
          exfalso
          have hmemT : u₁ ∈ T := hab ▸ (eB ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, by simp [A, hb1, hb2]⟩⟩).2
          exact Finset.disjoint_left.mp hdisj_T hmemT (by simp [U])
    · by_cases ha2 : a = i₂
      · by_cases hb1 : b = i₁
        · simp only [f, ha2, hb1, hi_ne.symm, ↓reduceDIte] at hab; exact absurd hab.symm hu_ne
        · by_cases hb2 : b = i₂
          · exact ha2.trans hb2.symm
          · simp only [f, ha2, hb1, hb2, hi_ne.symm, ↓reduceDIte] at hab
            exfalso
            have hmemT : u₂ ∈ T := hab ▸ (eB ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, by simp [A, hb1, hb2]⟩⟩).2
            exact Finset.disjoint_left.mp hdisj_T hmemT (by simp [U])
      · by_cases hb1 : b = i₁
        · simp only [f, ha1, ha2, hb1, ↓reduceDIte] at hab
          exfalso
          have hmemT : u₁ ∈ T := hab.symm ▸ (eB ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, by simp [A, ha1, ha2]⟩⟩).2
          exact Finset.disjoint_left.mp hdisj_T hmemT (by simp [U])
        · by_cases hb2 : b = i₂
          · simp only [f, ha1, ha2, hb2, hi_ne.symm, ↓reduceDIte] at hab
            exfalso
            have hmemT : u₂ ∈ T := hab.symm ▸ (eB ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, by simp [A, ha1, ha2]⟩⟩).2
            exact Finset.disjoint_left.mp hdisj_T hmemT (by simp [U])
          · simp only [f, ha1, ha2, hb1, hb2, ↓reduceDIte] at hab
            have heq := eB.injective (Subtype.ext hab)
            exact congr_arg Subtype.val heq
  apply hJfree
  refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
  intro a b hab
  rcases hall_eq a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [f, ↓reduceDIte, hi_ne.symm]; exact hHadj
  · simp only [f, ↓reduceDIte, hi_ne.symm]; exact hHadj.symm

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1.H1 := by
  intro q G hGbip hG2 ⟨v, hdeg⟩
  have hq_ge3 : 3 ≤ q := by
    by_contra hlt
    push Not at hlt
    have hq_le2 : q ≤ 2 := by omega
    have hle1 : G.edgeFinset.card ≤ 1 := by
      have hsub : G.edgeFinset ⊆ (Finset.univ : Finset (Fin q)).offDiag.image (fun p ↦ s(p.1, p.2)) := by
        intro e he
        rcases e with ⟨a, b⟩
        rw [SimpleGraph.mem_edgeFinset] at he
        rw [Finset.mem_image]
        exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨Finset.mem_univ a, Finset.mem_univ b, he.ne⟩, rfl⟩
      have hoff : ((Finset.univ : Finset (Fin q)).offDiag.image (fun p ↦ s(p.1, p.2))).card ≤ 1 := by
        interval_cases q
        · exact absurd v.isLt (by omega)
        · decide
        · decide
      exact (Finset.card_le_card hsub).trans hoff
    omega
  let r : ℕ := q - 1
  have hr : r + 1 = q := by omega
  have hr_pos : 0 < r := by omega
  have hcard_sub : Fintype.card {x : Fin q // x ≠ v} = r := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  let e : {x : Fin q // x ≠ v} ≃ Fin r := Fintype.equivFinOfCardEq hcard_sub
  let J : SimpleGraph (Fin r) := SimpleGraph.comap (fun i : Fin r ↦ (e.symm i).1) G
  have hJG : J ⊑ G :=
    ⟨⟨⟨fun i ↦ (e.symm i).1, fun h ↦ h⟩, fun a b h ↦ e.symm.injective (Subtype.ext h)⟩⟩
  have hJbip : J.IsBipartite := by
    obtain ⟨c⟩ := hGbip
    exact ⟨c.comp ⟨fun i ↦ (e.symm i).1, fun h ↦ h⟩⟩
  have hex_le : ∀ n, extremalNumber n J ≤ extremalNumber n G :=
    fun n ↦ hJG.extremalNumber_le
  have hex_up : ∀ n, extremalNumber n G ≤ extremalNumber n J + q * n :=
    fun n ↦ extremalNumber_le_delete_low_deg hdeg hr_pos e hr
  by_cases hJ2 : 2 ≤ J.edgeFinset.card
  · right
    refine ⟨r, J, by omega, hJbip, hJ2, ?_⟩
    refine Asymptotics.IsBigO.of_bound (q : ℝ) ?_
    filter_upwards with n
    have h1 : (extremalNumber n J : ℝ) ≤ (extremalNumber n G : ℝ) := by exact_mod_cast hex_le n
    have h2 : (extremalNumber n G : ℝ) ≤ (extremalNumber n J : ℝ) + (q : ℝ) * (n : ℝ) := by
      exact_mod_cast hex_up n
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Nat.cast_nonneg n), abs_of_nonpos (by linarith)]
    linarith
  · left
    -- J has at least 1 edge since G has ≥ 2 edges and at most 1 is incident to v
    have hJ1 : J.edgeFinset.card = 1 := by
      have hinc_le : (G.edgeFinset.filter (fun ed ↦ v ∈ ed)).card ≤ 1 := by
        have hsub : G.edgeFinset.filter (fun ed ↦ v ∈ ed) ⊆
            (G.neighborFinset v).image (fun u ↦ s(v, u)) := by
          intro ed hed
          rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hed
          rcases ed with ⟨a, b⟩
          simp only [Sym2.mem_iff] at hed
          rw [Finset.mem_image]
          rcases hed.2 with rfl | rfl
          · exact ⟨b, (SimpleGraph.mem_neighborFinset G v b).mpr hed.1, rfl⟩
          · exact ⟨a, (SimpleGraph.mem_neighborFinset G v a).mpr hed.1.symm, Sym2.eq_swap⟩
        calc (G.edgeFinset.filter (fun ed ↦ v ∈ ed)).card
            ≤ ((G.neighborFinset v).image (fun u ↦ s(v, u))).card := Finset.card_le_card hsub
          _ ≤ (G.neighborFinset v).card := Finset.card_image_le
          _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
          _ ≤ 1 := by omega
      have hpart := Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (p := fun ed ↦ v ∈ ed)
      have hnoninc_pos : 0 < (G.edgeFinset.filter (fun ed ↦ v ∉ ed)).card := by omega
      obtain ⟨ed, hed⟩ := Finset.card_pos.mp hnoninc_pos
      rcases ed with ⟨a, b⟩
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hed
      have ha : a ≠ v := fun h ↦ hed.2 (by simp [h])
      have hb : b ≠ v := fun h ↦ hed.2 (by simp [h])
      have hJadj : J.Adj (e ⟨a, ha⟩) (e ⟨b, hb⟩) := by
        change G.Adj (e.symm (e ⟨a, ha⟩)).1 (e.symm (e ⟨b, hb⟩)).1
        simpa using hed.1
      have hJpos : 0 < J.edgeFinset.card :=
        Finset.card_pos.mpr ⟨s(e ⟨a, ha⟩, e ⟨b, hb⟩), SimpleGraph.mem_edgeFinset.mpr hJadj⟩
      omega
    refine Asymptotics.IsBigO.of_bound (q : ℝ) ?_
    filter_upwards [eventually_ge_atTop r] with n hnr
    have h0 : extremalNumber n J = 0 := extremalNumber_eq_zero_of_one_edge hnr hJ1
    have hle : extremalNumber n G ≤ q * n := by
      have := hex_up n
      omega
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hle
