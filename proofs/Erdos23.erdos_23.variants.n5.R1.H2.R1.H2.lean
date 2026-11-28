import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1_H2_R1

-- Step Erdos23.erdos_23.variants.n5.R1.H2.R1.H2: hypothesis H2 of reduction Erdos23.erdos_23.variants.n5.R1.H2.R1
-- Credit: @KevinBigham

namespace Erdos23H2R1H2Proof

open SimpleGraph Finset
open scoped Classical

private abbrev V := Fin 25

private lemma sameSide_mk (S : Finset V) (x y : V) :
    (∀ a ∈ s(x, y), ∀ b ∈ s(x, y), (a ∈ S ↔ b ∈ S)) ↔ (x ∈ S ↔ y ∈ S) := by
  simp only [Sym2.mem_iff]
  constructor
  · intro h
    exact h x (Or.inl rfl) y (Or.inr rfl)
  · rintro h a (rfl | rfl) b (rfl | rfl) <;> tauto

private noncomputable def mono (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card

private noncomputable def edgesIn (G : SimpleGraph V) (X : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ X)).card

private noncomputable def degIn (G : SimpleGraph V) (X : Finset V) (u : V) : ℕ :=
  (G.neighborFinset u ∩ X).card

private noncomputable def edgesBetween (G : SimpleGraph V) (X Y : Finset V) :
    Finset (Sym2 V) :=
  X.biUnion (fun x => (G.neighborFinset x ∩ Y).image (fun y => s(x, y)))

private lemma mem_edgesBetween {G : SimpleGraph V} {X Y : Finset V} {a b : V} :
    s(a, b) ∈ edgesBetween G X Y ↔
      G.Adj a b ∧ ((a ∈ X ∧ b ∈ Y) ∨ (b ∈ X ∧ a ∈ Y)) := by
  simp only [edgesBetween, mem_biUnion, mem_image, mem_inter, mem_neighborFinset, Sym2.eq_iff]
  constructor
  · rintro ⟨x, hx, y, ⟨hxy, hy⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
    · exact ⟨hxy.symm, Or.inr ⟨hx, hy⟩⟩
  · rintro ⟨hab, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩
    · exact ⟨a, ha, b, ⟨hab, hb⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨b, hb, a, ⟨hab.symm, ha⟩, Or.inr ⟨rfl, rfl⟩⟩

private lemma card_edgesBetween {G : SimpleGraph V} {X Y : Finset V} (hdisj : Disjoint X Y) :
    (edgesBetween G X Y).card = ∑ x ∈ X, degIn G Y x := by
  unfold edgesBetween degIn
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.card_image_of_injective _ fun y₁ y₂ h => ?_
    rw [Sym2.eq_iff] at h
    rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · intro x₁ hx₁ x₂ hx₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [mem_image, mem_inter, mem_neighborFinset] at he₁ he₂
    rcases he₁ with ⟨y₁, ⟨_, hy₁⟩, rfl⟩
    rcases he₂ with ⟨y₂, ⟨_, hy₂⟩, heq⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · exact Finset.disjoint_left.mp hdisj hx₁ hy₂

private lemma card_edgesBetween_eq_filter_prod {G : SimpleGraph V} {X Y : Finset V}
    (hdisj : Disjoint X Y) :
    (edgesBetween G X Y).card = ((X ×ˢ Y).filter (fun p => G.Adj p.1 p.2)).card := by
  symm
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product] at hp
    rw [mem_edgesBetween]
    exact ⟨hp.2, Or.inl hp.1⟩
  · intro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ h
    simp only [mem_filter, mem_product] at hp₁ hp₂
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hp₂.1.2 (Finset.disjoint_left.mp hdisj hp₁.1.1)
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgesBetween] at he
      rcases he with ⟨hab, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
      · exact ⟨(a, b), by simp [mem_filter, mem_product, ha, hb, hab], rfl⟩
      · exact ⟨(b, a), by simp [mem_filter, mem_product, ha, hb, hab.symm], Sym2.eq_swap⟩

private lemma edgesIn_union_of_indep {G : SimpleGraph V} {X Y : Finset V}
    (hX : ∀ a ∈ X, ∀ b ∈ X, ¬ G.Adj a b) (hY : ∀ a ∈ Y, ∀ b ∈ Y, ¬ G.Adj a b) :
    edgesIn G (X ∪ Y) = (edgesBetween G X Y).card := by
  unfold edgesIn
  congr 1
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [mem_filter, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp,
      forall_eq, mem_union, mem_edgesBetween]
    constructor
    · rintro ⟨hab, ha | ha, hb | hb⟩
      · exact absurd hab (hX a ha b hb)
      · exact ⟨hab, Or.inl ⟨ha, hb⟩⟩
      · exact ⟨hab, Or.inr ⟨hb, ha⟩⟩
      · exact absurd hab (hY a ha b hb)
    · rintro ⟨hab, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
      · exact ⟨hab, Or.inl ha, Or.inr hb⟩
      · exact ⟨hab, Or.inr ha, Or.inl hb⟩

private lemma edgesIn_eq_zero_of_indep {G : SimpleGraph V} {X : Finset V}
    (hX : ∀ a ∈ X, ∀ b ∈ X, ¬ G.Adj a b) : edgesIn G X = 0 := by
  unfold edgesIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    intro hall
    exact hX x (hall x (Sym2.mem_mk_left x y)) y (hall y (Sym2.mem_mk_right x y)) he

private lemma mono_nbhd_eq_edgesIn {G : SimpleGraph V} (hG : G.CliqueFree 3) (v : V) :
    mono G (G.neighborFinset v) = edgesIn G (insert v (G.neighborFinset v))ᶜ := by
  unfold mono edgesIn
  congr 1
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [mem_filter, mem_edgeFinset, mem_edgeSet]
    rw [sameSide_mk]
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, mem_compl, mem_insert, not_or,
      mem_neighborFinset]
    constructor
    · rintro ⟨hab, hiff⟩
      have hna : ¬ G.Adj v a := by
        intro hva
        have hvb : G.Adj v b := hiff.mp hva
        exact hG {v, a, b} (is3Clique_triple_iff.mpr ⟨hva, hvb, hab⟩)
      have hnb : ¬ G.Adj v b := fun hvb => hna (hiff.mpr hvb)
      have hav : a ≠ v := fun h => hnb (h ▸ hab)
      have hbv : b ≠ v := fun h => hna (h ▸ hab.symm)
      exact ⟨hab, ⟨hav, hna⟩, ⟨hbv, hnb⟩⟩
    · rintro ⟨hab, ⟨_, hna⟩, ⟨_, hnb⟩⟩
      exact ⟨hab, ⟨fun h => absurd h hna, fun h => absurd h hnb⟩⟩

private lemma mono_cut_eq {G : SimpleGraph V} (hG : G.CliqueFree 3) (v : V)
    {A B N_B : Finset V}
    (hAB_disj : Disjoint A B)
    (hAB_union : A ∪ B = (insert v (G.neighborFinset v))ᶜ)
    (hNB_sub : N_B ⊆ G.neighborFinset v)
    (inS : Bool) :
    let N := G.neighborFinset v
    let N_A := N \ N_B
    let S := if inS then insert v (A ∪ N_B) else A ∪ N_B
    mono G S =
      edgesIn G A + edgesIn G B +
      (∑ u ∈ N_B, degIn G A u) + (∑ u ∈ N_A, degIn G B u) +
      (if inS then N_B.card else N_A.card) := by
  intro N N_A S
  have hvN : v ∉ N := fun h => G.loopless.irrefl v ((mem_neighborFinset G v v).mp h)
  have hM_mem : ∀ x : V, x ∈ A ∪ B ↔ x ≠ v ∧ x ∉ N := by
    intro x
    rw [hAB_union, mem_compl, mem_insert, not_or]
  have hvA : v ∉ A := fun h => ((hM_mem v).mp (mem_union_left B h)).1 rfl
  have hvB : v ∉ B := fun h => ((hM_mem v).mp (mem_union_right A h)).1 rfl
  have hvNB : v ∉ N_B := fun h => hvN (hNB_sub h)
  have hAN : Disjoint A N := by
    rw [Finset.disjoint_left]
    intro x hxA hxN
    exact ((hM_mem x).mp (mem_union_left B hxA)).2 hxN
  have hBN : Disjoint B N := by
    rw [Finset.disjoint_left]
    intro x hxB hxN
    exact ((hM_mem x).mp (mem_union_right A hxB)).2 hxN
  have hNA_sub : N_A ⊆ N := sdiff_subset
  have hdisj_NB_A : Disjoint N_B A := hAN.symm.mono_left hNB_sub
  have hdisj_NA_B : Disjoint N_A B := hBN.symm.mono_left hNA_sub
  have hind_N : ∀ x ∈ N, ∀ y ∈ N, ¬ G.Adj x y := by
    intro x hx y hy hxy
    exact hG {v, x, y} (is3Clique_triple_iff.mpr
      ⟨(mem_neighborFinset G v x).mp hx, (mem_neighborFinset G v y).mp hy, hxy⟩)
  let E₁ : Finset (Sym2 V) := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ A)
  let E₂ : Finset (Sym2 V) := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ B)
  let E₃ : Finset (Sym2 V) := edgesBetween G N_B A
  let E₄ : Finset (Sym2 V) := edgesBetween G N_A B
  let N_v : Finset V := if inS then N_B else N_A
  let E₅ : Finset (Sym2 V) := N_v.image (fun u => s(v, u))
  have hNv_sub : N_v ⊆ N := by cases inS <;> assumption
  have hmem_S : ∀ x : V, x ∈ S ↔ (inS = true ∧ x = v) ∨ x ∈ A ∨ x ∈ N_B := by
    intro x
    cases inS <;> simp [S, mem_insert, mem_union]
  have hnotS_B : ∀ x ∈ B, x ∉ S := by
    intro x hxB hxS
    rw [hmem_S] at hxS
    rcases hxS with ⟨_, rfl⟩ | hxA | hxNB
    · exact hvB hxB
    · exact Finset.disjoint_left.mp hAB_disj hxA hxB
    · exact Finset.disjoint_left.mp hBN hxB (hNB_sub hxNB)
  have hnotS_NA : ∀ x ∈ N_A, x ∉ S := by
    intro x hxNA hxS
    rw [hmem_S] at hxS
    rcases hxS with ⟨_, rfl⟩ | hxA | hxNB
    · exact hvN (hNA_sub hxNA)
    · exact Finset.disjoint_left.mp hAN hxA (hNA_sub hxNA)
    · exact (mem_sdiff.mp hxNA).2 hxNB
  have hv_mem_S : v ∈ S ↔ inS = true := by
    rw [hmem_S]
    simp [hvA, hvNB]
  have hmem_E₅ : ∀ a b : V, s(a, b) ∈ E₅ ↔
      (a = v ∧ b ∈ N_v) ∨ (b = v ∧ a ∈ N_v) := by
    intro a b
    simp only [E₅, mem_image, Sym2.eq_iff]
    constructor
    · rintro ⟨u, hu, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact Or.inl ⟨rfl, hu⟩
      · exact Or.inr ⟨rfl, hu⟩
    · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
      · exact ⟨b, hb, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩
  have hpart : ∀ x : V, x = v ∨ x ∈ N_B ∨ x ∈ N_A ∨ x ∈ A ∨ x ∈ B := by
    intro x
    by_cases hxv : x = v
    · exact Or.inl hxv
    · by_cases hxN : x ∈ N
      · by_cases hxNB : x ∈ N_B
        · exact Or.inr (Or.inl hxNB)
        · exact Or.inr (Or.inr (Or.inl (mem_sdiff.mpr ⟨hxN, hxNB⟩)))
      · have hxM : x ∈ A ∪ B := (hM_mem x).mpr ⟨hxv, hxN⟩
        rcases mem_union.mp hxM with hxA | hxB
        · exact Or.inr (Or.inr (Or.inr (Or.inl hxA)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hxB)))
  have hdecomp : G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) =
      (((E₁ ∪ E₂) ∪ E₃) ∪ E₄) ∪ E₅ := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_filter, mem_edgeFinset, mem_edgeSet, mem_union, E₁, E₂, E₃, E₄]
      rw [sameSide_mk]
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, mem_edgesBetween, hmem_E₅]
      constructor
      · rintro ⟨hab, hiff⟩
        rcases hpart a with hav | haNB | haNA | haA | haB
        · have hbN : b ∈ N := (mem_neighborFinset G v b).mpr (hav ▸ hab)
          cases hin : inS
          · have hv_not : a ∉ S := by
              intro h; rw [hav, hv_mem_S, hin] at h; exact Bool.noConfusion h
            have hb_not : b ∉ S := fun h => hv_not (hiff.mpr h)
            have hb_notNB : b ∉ N_B := fun h => hb_not ((hmem_S b).mpr (Or.inr (Or.inr h)))
            exact Or.inr (Or.inl ⟨hav, by simp [N_v, hin, N_A, hbN, hb_notNB]⟩)
          · have hv_in : a ∈ S := by rw [hav, hv_mem_S, hin]
            have hb_in : b ∈ S := hiff.mp hv_in
            have hbNB : b ∈ N_B := by
              rw [hmem_S] at hb_in
              rcases hb_in with ⟨_, hbv⟩ | hbA | hbNB
              · exact absurd (hbv ▸ hbN) hvN
              · exact absurd hbA (Finset.disjoint_right.mp hAN hbN)
              · exact hbNB
            exact Or.inr (Or.inl ⟨hav, by simp [N_v, hin, hbNB]⟩)
        · have haN : a ∈ N := hNB_sub haNB
          have haS : a ∈ S := (hmem_S a).mpr (Or.inr (Or.inr haNB))
          have hbS : b ∈ S := hiff.mp haS
          rcases hpart b with hbv | hbNB | hbNA | hbA | hbB
          · cases hin : inS
            · exfalso; rw [hbv, hv_mem_S, hin] at hbS; exact Bool.noConfusion hbS
            · exact Or.inr (Or.inr ⟨hbv, by simp [N_v, hin, haNB]⟩)
          · exact absurd hab (hind_N a haN b (hNB_sub hbNB))
          · exact absurd hab (hind_N a haN b (hNA_sub hbNA))
          · exact Or.inl (Or.inl (Or.inr ⟨hab, Or.inl ⟨haNB, hbA⟩⟩))
          · exact absurd hbS (hnotS_B b hbB)
        · have haN : a ∈ N := hNA_sub haNA
          have hb_notS : b ∉ S := fun h => hnotS_NA a haNA (hiff.mpr h)
          rcases hpart b with hbv | hbNB | hbNA | hbA | hbB
          · cases hin : inS
            · exact Or.inr (Or.inr ⟨hbv, by simp [N_v, hin, haNA]⟩)
            · exact absurd (hv_mem_S.mpr hin) (hbv ▸ hb_notS)
          · exact absurd hab (hind_N a haN b (hNB_sub hbNB))
          · exact absurd hab (hind_N a haN b (hNA_sub hbNA))
          · exact absurd ((hmem_S b).mpr (Or.inr (Or.inl hbA))) hb_notS
          · exact Or.inl (Or.inr ⟨hab, Or.inl ⟨haNA, hbB⟩⟩)
        · have hbS : b ∈ S := hiff.mp ((hmem_S a).mpr (Or.inr (Or.inl haA)))
          rcases hpart b with hbv | hbNB | hbNA | hbA | hbB
          · exact absurd ((mem_neighborFinset G v a).mpr (hbv ▸ hab.symm))
              (Finset.disjoint_left.mp hAN haA)
          · exact Or.inl (Or.inl (Or.inr ⟨hab, Or.inr ⟨hbNB, haA⟩⟩))
          · exact absurd hbS (hnotS_NA b hbNA)
          · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hab, haA, hbA⟩)))
          · exact absurd hbS (hnotS_B b hbB)
        · have hb_notS : b ∉ S := fun h => hnotS_B a haB (hiff.mpr h)
          rcases hpart b with hbv | hbNB | hbNA | hbA | hbB
          · exact absurd ((mem_neighborFinset G v a).mpr (hbv ▸ hab.symm))
              (Finset.disjoint_left.mp hBN haB)
          · exact absurd ((hmem_S b).mpr (Or.inr (Or.inr hbNB))) hb_notS
          · exact Or.inl (Or.inr ⟨hab, Or.inr ⟨hbNA, haB⟩⟩)
          · exact absurd ((hmem_S b).mpr (Or.inr (Or.inl hbA))) hb_notS
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hab, haB, hbB⟩)))
      · rintro ((((⟨hab, haA, hbA⟩ | ⟨hab, haB, hbB⟩) | ⟨hab, ⟨haNB, hbA⟩ | ⟨hbNB, haA⟩⟩) |
          ⟨hab, ⟨haNA, hbB⟩ | ⟨hbNA, haB⟩⟩) | (⟨hav, hbNv⟩ | ⟨hbv, haNv⟩))
        · exact ⟨hab, by simp [hmem_S, haA, hbA]⟩
        · exact ⟨hab, by simp [hnotS_B a haB, hnotS_B b hbB]⟩
        · exact ⟨hab, by simp [hmem_S, haNB, hbA]⟩
        · exact ⟨hab, by simp [hmem_S, hbNB, haA]⟩
        · exact ⟨hab, by simp [hnotS_NA a haNA, hnotS_B b hbB]⟩
        · exact ⟨hab, by simp [hnotS_B a haB, hnotS_NA b hbNA]⟩
        · have hvb : G.Adj a b := hav ▸ (mem_neighborFinset G v b).mp (hNv_sub hbNv)
          refine ⟨hvb, ?_⟩
          cases hin : inS
          · simp only [N_v, hin, Bool.false_eq_true, ↓reduceIte] at hbNv
            have ha_not : a ∉ S := by
              intro h; rw [hav, hv_mem_S, hin] at h; exact Bool.noConfusion h
            simp [ha_not, hnotS_NA b hbNv]
          · simp only [N_v, hin, ↓reduceIte] at hbNv
            have ha_in : a ∈ S := by rw [hav, hv_mem_S, hin]
            have hb_in : b ∈ S := (hmem_S b).mpr (Or.inr (Or.inr hbNv))
            simp [ha_in, hb_in]
        · have hab : G.Adj a b := hbv ▸ ((mem_neighborFinset G v a).mp (hNv_sub haNv)).symm
          refine ⟨hab, ?_⟩
          cases hin : inS
          · simp only [N_v, hin, Bool.false_eq_true, ↓reduceIte] at haNv
            have hb_not : b ∉ S := by
              intro h; rw [hbv, hv_mem_S, hin] at h; exact Bool.noConfusion h
            simp [hnotS_NA a haNv, hb_not]
          · simp only [N_v, hin, ↓reduceIte] at haNv
            have ha_in : a ∈ S := (hmem_S a).mpr (Or.inr (Or.inr haNv))
            have hb_in : b ∈ S := by rw [hbv, hv_mem_S, hin]
            simp [ha_in, hb_in]
  have hd12 : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    induction e using Sym2.ind with
    | h a b =>
      simp only [E₁, E₂, mem_filter, Sym2.mem_iff, forall_eq_or_imp, forall_eq] at h1 h2
      exact Finset.disjoint_left.mp hAB_disj h1.2.1 h2.2.1
  have hd12_3 : Disjoint (E₁ ∪ E₂) E₃ := by
    rw [Finset.disjoint_left]
    intro e h12 h3
    induction e using Sym2.ind with
    | h a b =>
      simp only [E₁, E₂, E₃, mem_union, mem_filter, Sym2.mem_iff, forall_eq_or_imp,
        forall_eq, mem_edgesBetween] at h12 h3
      rcases h12 with ⟨_, haA, hbA⟩ | ⟨_, haB, hbB⟩
      · rcases h3.2 with ⟨haNB, _⟩ | ⟨hbNB, _⟩
        · exact Finset.disjoint_left.mp hAN haA (hNB_sub haNB)
        · exact Finset.disjoint_left.mp hAN hbA (hNB_sub hbNB)
      · rcases h3.2 with ⟨_, hbA⟩ | ⟨_, haA⟩
        · exact Finset.disjoint_left.mp hAB_disj hbA hbB
        · exact Finset.disjoint_left.mp hAB_disj haA haB
  have hd123_4 : Disjoint ((E₁ ∪ E₂) ∪ E₃) E₄ := by
    rw [Finset.disjoint_left]
    intro e h123 h4
    induction e using Sym2.ind with
    | h a b =>
      simp only [E₁, E₂, E₃, E₄, mem_union, mem_filter, Sym2.mem_iff, forall_eq_or_imp,
        forall_eq, mem_edgesBetween] at h123 h4
      rcases h123 with (⟨_, haA, hbA⟩ | ⟨_, haB, hbB⟩) | ⟨_, ⟨haNB, hbA⟩ | ⟨hbNB, haA⟩⟩
      · rcases h4.2 with ⟨_, hbB⟩ | ⟨_, haB⟩
        · exact Finset.disjoint_left.mp hAB_disj hbA hbB
        · exact Finset.disjoint_left.mp hAB_disj haA haB
      · rcases h4.2 with ⟨haNA, _⟩ | ⟨hbNA, _⟩
        · exact Finset.disjoint_left.mp hBN haB (hNA_sub haNA)
        · exact Finset.disjoint_left.mp hBN hbB (hNA_sub hbNA)
      · rcases h4.2 with ⟨haNA, _⟩ | ⟨hbNA, _⟩
        · exact (mem_sdiff.mp haNA).2 haNB
        · exact Finset.disjoint_left.mp hAN hbA (hNA_sub hbNA)
      · rcases h4.2 with ⟨haNA, _⟩ | ⟨hbNA, _⟩
        · exact Finset.disjoint_left.mp hAN haA (hNA_sub haNA)
        · exact (mem_sdiff.mp hbNA).2 hbNB
  have hd1234_5 : Disjoint (((E₁ ∪ E₂) ∪ E₃) ∪ E₄) E₅ := by
    rw [Finset.disjoint_left]
    intro e h1234 h5
    induction e using Sym2.ind with
    | h a b =>
      simp only [E₁, E₂, E₃, E₄, mem_union, mem_filter, Sym2.mem_iff, forall_eq_or_imp,
        forall_eq, mem_edgesBetween, hmem_E₅] at h1234 h5
      rcases h5 with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
      · rcases h1234 with ((⟨_, h, _⟩ | ⟨_, h, _⟩) | ⟨_, ⟨h, _⟩ | ⟨_, h⟩⟩) | ⟨_, ⟨h, _⟩ | ⟨_, h⟩⟩
        · exact hvA h
        · exact hvB h
        · exact hvN (hNB_sub h)
        · exact hvA h
        · exact hvN (hNA_sub h)
        · exact hvB h
      · rcases h1234 with ((⟨_, _, h⟩ | ⟨_, _, h⟩) | ⟨_, ⟨_, h⟩ | ⟨h, _⟩⟩) | ⟨_, ⟨_, h⟩ | ⟨h, _⟩⟩
        · exact hvA h
        · exact hvB h
        · exact hvA h
        · exact hvN (hNB_sub h)
        · exact hvB h
        · exact hvN (hNA_sub h)
  have hcard_E₅ : E₅.card = if inS then N_B.card else N_A.card := by
    have hinj : Function.Injective (fun u : V => s(v, u)) := by
      intro u₁ u₂ h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [Finset.card_image_of_injective _ hinj]
    cases inS <;> rfl
  unfold mono
  rw [hdecomp, Finset.card_union_of_disjoint hd1234_5, Finset.card_union_of_disjoint hd123_4,
    Finset.card_union_of_disjoint hd12_3, Finset.card_union_of_disjoint hd12,
    card_edgesBetween hdisj_NB_A, card_edgesBetween hdisj_NA_B, hcard_E₅]
  rfl

private lemma rect_subset_nonedges {G : SimpleGraph V} (hG : G.CliqueFree 3)
    (A B : Finset V) (u : V) :
    (G.neighborFinset u ∩ A) ×ˢ (G.neighborFinset u ∩ B) ⊆
      (A ×ˢ B).filter (fun p => ¬ G.Adj p.1 p.2) := by
  intro ⟨a, b⟩ hp
  simp only [mem_product, mem_inter, mem_neighborFinset, mem_filter] at hp ⊢
  refine ⟨⟨hp.1.2, hp.2.2⟩, fun hab => ?_⟩
  exact hG {u, a, b} (is3Clique_triple_iff.mpr ⟨hp.1.1, hp.2.1, hab⟩)

private lemma mul_deg_add_edges_le {G : SimpleGraph V} (hG : G.CliqueFree 3)
    {A B : Finset V} (hdisj : Disjoint A B)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) (hB : ∀ a ∈ B, ∀ b ∈ B, ¬ G.Adj a b) (u : V) :
    degIn G A u * degIn G B u + edgesIn G (A ∪ B) ≤ A.card * B.card := by
  have hsub := rect_subset_nonedges hG A B u
  have h1 : degIn G A u * degIn G B u ≤ ((A ×ˢ B).filter (fun p => ¬ G.Adj p.1 p.2)).card := by
    unfold degIn
    rw [← Finset.card_product]
    exact Finset.card_le_card hsub
  have h2 : edgesIn G (A ∪ B) = ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card := by
    rw [edgesIn_union_of_indep hA hB, card_edgesBetween_eq_filter_prod hdisj]
  have h3 := Finset.card_filter_add_card_filter_not (s := A ×ˢ B) (fun p => G.Adj p.1 p.2)
  rw [Finset.card_product] at h3
  omega

private lemma case_small_T {G : SimpleGraph V} (hG : G.CliqueFree 3) (v : V)
    (hN_card : (G.neighborFinset v).card = 13)
    {A B : Finset V} (hAB_disj : Disjoint A B)
    (hAB_union : A ∪ B = (insert v (G.neighborFinset v))ᶜ)
    (hA_ind : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b)
    (hB_ind : ∀ a ∈ B, ∀ b ∈ B, ¬ G.Adj a b)
    (hdeg_mul : ∀ u : V, degIn G A u * degIn G B u ≤ 4)
    (hT : ((G.neighborFinset v).filter (fun u => degIn G A u = 2 ∧ degIn G B u = 2)).card ≤ 6) :
    ∃ S : Finset V, mono G S ≤ 25 := by
  set N : Finset V := G.neighborFinset v
  set T : Finset V := N.filter (fun u => degIn G A u = 2 ∧ degIn G B u = 2)
  set N_B : Finset V := N.filter (fun u => degIn G A u ≤ degIn G B u)
  set N_A : Finset V := N \ N_B
  let S₁ : Finset V := A ∪ N_B
  let S₂ : Finset V := insert v (A ∪ N_B)
  have hNB_sub : N_B ⊆ N := Finset.filter_subset _ _
  have h1 : mono G S₁ = edgesIn G A + edgesIn G B +
      (∑ u ∈ N_B, degIn G A u) + (∑ u ∈ N_A, degIn G B u) + N_A.card := by
    simpa [S₁, N, N_A] using mono_cut_eq hG v hAB_disj hAB_union hNB_sub false
  have h2 : mono G S₂ = edgesIn G A + edgesIn G B +
      (∑ u ∈ N_B, degIn G A u) + (∑ u ∈ N_A, degIn G B u) + N_B.card := by
    simpa [S₂, N, N_A] using mono_cut_eq hG v hAB_disj hAB_union hNB_sub true
  have hEA : edgesIn G A = 0 := edgesIn_eq_zero_of_indep hA_ind
  have hEB : edgesIn G B = 0 := edgesIn_eq_zero_of_indep hB_ind
  have hdisjN : Disjoint N_B N_A := Finset.disjoint_sdiff
  have hunionN : N_B ∪ N_A = N := Finset.union_sdiff_of_subset hNB_sub
  have hsum_min : (∑ u ∈ N_B, degIn G A u) + (∑ u ∈ N_A, degIn G B u) =
      ∑ u ∈ N, min (degIn G A u) (degIn G B u) := by
    rw [← hunionN, Finset.sum_union hdisjN]
    congr 1
    · refine Finset.sum_congr rfl fun u hu => (min_eq_left (mem_filter.mp hu).2).symm
    · refine Finset.sum_congr rfl fun u hu => ?_
      have hgt : ¬ (degIn G A u ≤ degIn G B u) := fun hle =>
        (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1, hle⟩)
      exact (min_eq_right (le_of_not_ge hgt)).symm
  have hN_split : N_A.card + N_B.card = 13 := by
    have h := Finset.card_union_of_disjoint hdisjN
    rw [hunionN, hN_card] at h
    omega
  have hmin_bound : ∑ u ∈ N, min (degIn G A u) (degIn G B u) ≤ 13 + T.card := by
    have hbound : ∀ u ∈ N,
        min (degIn G A u) (degIn G B u) ≤ 1 + if u ∈ T then 1 else 0 := by
      intro u hu
      have hm := hdeg_mul u
      by_cases huT : u ∈ T
      · rw [if_pos huT]
        have ⟨ha, hb⟩ := (mem_filter.mp huT).2
        omega
      · rw [if_neg huT]
        have hnot : ¬ (degIn G A u = 2 ∧ degIn G B u = 2) := fun h =>
          huT (mem_filter.mpr ⟨hu, h⟩)
        have hle1 : min (degIn G A u) (degIn G B u) ≤ 1 := by
          by_contra hgt
          push Not at hgt
          have ha2 : 2 ≤ degIn G A u := le_trans hgt (min_le_left _ _)
          have hb2 : 2 ≤ degIn G B u := le_trans hgt (min_le_right _ _)
          have ha_eq : degIn G A u = 2 := by nlinarith
          have hb_eq : degIn G B u = 2 := by nlinarith
          exact hnot ⟨ha_eq, hb_eq⟩
        omega
    have hTf : N.filter (fun u => u ∈ T) = T := by
      ext u
      simp [T]
    calc
      ∑ u ∈ N, min (degIn G A u) (degIn G B u)
          ≤ ∑ u ∈ N, (1 + if u ∈ T then 1 else 0) := Finset.sum_le_sum hbound
      _ = N.card + (N.filter (fun u => u ∈ T)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.sum_boole, Nat.cast_id]
      _ = 13 + T.card := by rw [hN_card, hTf]
  have hsum_cuts : mono G S₁ + mono G S₂ ≤ 51 := by
    rw [h1, h2, hEA, hEB]
    omega
  rcases le_or_gt (mono G S₁) 25 with hS1 | hS1
  · exact ⟨S₁, hS1⟩
  · exact ⟨S₂, by omega⟩

private lemma case_large_T {G : SimpleGraph V} (hG : G.CliqueFree 3) (v : V)
    (hN_card : (G.neighborFinset v).card = 13)
    {A B : Finset V} (hAB_disj : Disjoint A B)
    (hAB_union : A ∪ B = (insert v (G.neighborFinset v))ᶜ)
    (hA_ind : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b)
    (hB_ind : ∀ a ∈ B, ∀ b ∈ B, ¬ G.Adj a b)
    (hAB_sum : A.card + B.card = 11) (hAB_le : A.card ≤ B.card)
    (hM_edges : 26 ≤ edgesIn G (A ∪ B))
    (hT_ge : 7 ≤ ((G.neighborFinset v).filter (fun u => degIn G A u = 2 ∧ degIn G B u = 2)).card) :
    ∃ S : Finset V, mono G S ≤ 25 := by
  set N : Finset V := G.neighborFinset v
  set T : Finset V := N.filter (fun u => degIn G A u = 2 ∧ degIn G B u = 2)
  have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u₀, hu₀⟩ := hT_ne
  have ⟨_, hu₀A, hu₀B⟩ := mem_filter.mp hu₀
  have hmul₀ : degIn G A u₀ * degIn G B u₀ = 4 := by rw [hu₀A, hu₀B]
  have hAB_prod_le : A.card * B.card ≤ 30 := by nlinarith
  have hAB_exact : A.card * B.card = 30 ∧ edgesIn G (A ∪ B) = 26 := by
    have h := mul_deg_add_edges_le hG hAB_disj hA_ind hB_ind u₀
    rw [hmul₀] at h
    omega
  have hA_card : A.card = 5 := by nlinarith
  set A₀ : Finset V := G.neighborFinset u₀ ∩ A
  set B₀ : Finset V := G.neighborFinset u₀ ∩ B
  have hA₀_sub : A₀ ⊆ A := Finset.inter_subset_right
  have hB₀_sub : B₀ ⊆ B := Finset.inter_subset_right
  have hA₀_card : A₀.card = 2 := hu₀A
  have hB₀_card : B₀.card = 2 := hu₀B
  have hnonedges_eq : A₀ ×ˢ B₀ = (A ×ˢ B).filter (fun p => ¬ G.Adj p.1 p.2) := by
    apply Finset.eq_of_subset_of_card_le (rect_subset_nonedges hG A B u₀)
    have h3 := Finset.card_filter_add_card_filter_not (s := A ×ˢ B) (fun p => G.Adj p.1 p.2)
    have h2 : edgesIn G (A ∪ B) = ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [edgesIn_union_of_indep hA_ind hB_ind, card_edgesBetween_eq_filter_prod hAB_disj]
    rw [Finset.card_product] at h3 ⊢
    rw [hA₀_card, hB₀_card]
    omega
  have h_all_edges : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b ↔ a ∈ A₀ ∧ b ∈ B₀ := by
    intro a ha b hb
    have hmem : (a, b) ∈ A₀ ×ˢ B₀ ↔ (a, b) ∈ (A ×ˢ B).filter (fun p => ¬ G.Adj p.1 p.2) := by
      rw [hnonedges_eq]
    simp only [mem_product, mem_filter, ha, hb, and_self, true_and] at hmem
    exact hmem.symm
  set A' : Finset V := A ∪ B₀
  set B' : Finset V := B \ B₀
  have hA'B'_disj : Disjoint A' B' := by
    rw [Finset.disjoint_union_left]
    exact ⟨hAB_disj.mono_right sdiff_subset, Finset.disjoint_sdiff⟩
  have hA'B'_union : A' ∪ B' = (insert v N)ᶜ := by
    rw [← hAB_union]
    ext x
    simp only [A', B', mem_union, mem_sdiff]
    constructor
    · rintro ((h | h) | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr (hB₀_sub h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · by_cases hx : x ∈ B₀
        · exact Or.inl (Or.inr hx)
        · exact Or.inr ⟨h, hx⟩
  have hEA' : edgesIn G A' ≤ 6 := by
    have hB₀_ind : ∀ a ∈ B₀, ∀ b ∈ B₀, ¬ G.Adj a b :=
      fun a ha b hb => hB_ind a (hB₀_sub ha) b (hB₀_sub hb)
    have hdisj_AB₀ : Disjoint A B₀ := hAB_disj.mono_right hB₀_sub
    rw [edgesIn_union_of_indep hA_ind hB₀_ind, card_edgesBetween_eq_filter_prod hdisj_AB₀]
    have hsub : (A ×ˢ B₀).filter (fun p => G.Adj p.1 p.2) ⊆ (A \ A₀) ×ˢ B₀ := by
      intro ⟨a, b⟩ hp
      simp only [mem_filter, mem_product, mem_sdiff] at hp ⊢
      refine ⟨⟨hp.1.1, fun ha₀ => ?_⟩, hp.1.2⟩
      exact (h_all_edges a hp.1.1 b (hB₀_sub hp.1.2)).mpr ⟨ha₀, hp.1.2⟩ hp.2
    calc
      ((A ×ˢ B₀).filter (fun p => G.Adj p.1 p.2)).card ≤ ((A \ A₀) ×ˢ B₀).card :=
        Finset.card_le_card hsub
      _ = (A \ A₀).card * B₀.card := Finset.card_product _ _
      _ = 6 := by
        rw [Finset.card_sdiff_of_subset hA₀_sub, hA_card, hA₀_card, hB₀_card]
  have hEB' : edgesIn G B' = 0 :=
    edgesIn_eq_zero_of_indep fun x hx y hy => hB_ind x (sdiff_subset hx) y (sdiff_subset hy)
  set N_B' : Finset V := N.filter (fun u => degIn G A' u + 1 ≤ degIn G B' u)
  set N_A' : Finset V := N \ N_B'
  let S₄ : Finset V := insert v (A' ∪ N_B')
  have hNB'_sub : N_B' ⊆ N := Finset.filter_subset _ _
  have hcut : mono G S₄ = edgesIn G A' + edgesIn G B' +
      (∑ u ∈ N_B', degIn G A' u) + (∑ u ∈ N_A', degIn G B' u) + N_B'.card := by
    simpa [S₄, N, N_A'] using mono_cut_eq hG v hA'B'_disj hA'B'_union hNB'_sub true
  have hsum_S₄ : (∑ u ∈ N_B', degIn G A' u) + (∑ u ∈ N_A', degIn G B' u) + N_B'.card =
      ∑ u ∈ N, min (degIn G A' u + 1) (degIn G B' u) := by
    have hdisjN : Disjoint N_B' N_A' := Finset.disjoint_sdiff
    have hunionN : N_B' ∪ N_A' = N := Finset.union_sdiff_of_subset hNB'_sub
    have hadd : (∑ u ∈ N_B', degIn G A' u) + N_B'.card =
        ∑ u ∈ N_B', (degIn G A' u + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rw [show (∑ u ∈ N_B', degIn G A' u) + (∑ u ∈ N_A', degIn G B' u) + N_B'.card =
        ((∑ u ∈ N_B', degIn G A' u) + N_B'.card) + (∑ u ∈ N_A', degIn G B' u) by omega,
      hadd, ← hunionN, Finset.sum_union hdisjN]
    congr 1
    · refine Finset.sum_congr rfl fun u hu => (min_eq_left (mem_filter.mp hu).2).symm
    · refine Finset.sum_congr rfl fun u hu => ?_
      have hgt : ¬ (degIn G A' u + 1 ≤ degIn G B' u) := fun hle =>
        (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1, hle⟩)
      exact (min_eq_right (le_of_not_ge hgt)).symm
  have hcost_T : ∀ u ∈ T, min (degIn G A' u + 1) (degIn G B' u) = 0 := by
    intro u hu
    have ⟨_, huA, huB⟩ := mem_filter.mp hu
    have hrect_eq : (G.neighborFinset u ∩ A) ×ˢ (G.neighborFinset u ∩ B) = A₀ ×ˢ B₀ := by
      rw [hnonedges_eq]
      apply Finset.eq_of_subset_of_card_le (rect_subset_nonedges hG A B u)
      rw [← hnonedges_eq, Finset.card_product, Finset.card_product, hA₀_card, hB₀_card]
      change 4 ≤ degIn G A u * degIn G B u
      rw [huA, huB]
    have hzero : degIn G B' u = 0 := by
      unfold degIn
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro b hb
      simp only [mem_inter, B', mem_sdiff] at hb
      have hneA : (G.neighborFinset u ∩ A).Nonempty := by
        apply Finset.card_pos.mp
        change 0 < degIn G A u
        omega
      obtain ⟨a, ha⟩ := hneA
      have hmem : (a, b) ∈ (G.neighborFinset u ∩ A) ×ˢ (G.neighborFinset u ∩ B) :=
        mem_product.mpr ⟨ha, mem_inter.mpr ⟨hb.1, hb.2.1⟩⟩
      rw [hrect_eq, mem_product] at hmem
      exact hb.2.2 hmem.2
    rw [hzero, min_eq_right (Nat.zero_le _)]
  have hcost_other : ∀ u ∈ N, min (degIn G A' u + 1) (degIn G B' u) ≤ 3 := by
    intro u _
    by_cases hB'0 : degIn G B' u = 0
    · rw [hB'0]; exact Nat.zero_le _
    · have hne : (G.neighborFinset u ∩ B').Nonempty := by
        apply Finset.card_pos.mp
        change 0 < degIn G B' u
        omega
      obtain ⟨b, hb⟩ := hne
      simp only [mem_inter, mem_neighborFinset, B', mem_sdiff] at hb
      have hnoA : ∀ a ∈ A, ¬ G.Adj u a := by
        intro a ha hua
        have hab : G.Adj a b := by
          by_contra hnab
          exact hb.2.2 ((h_all_edges a ha b hb.2.1).mp hnab).2
        exact hG {u, a, b} (is3Clique_triple_iff.mpr ⟨hua, hb.1, hab⟩)
      have hsub : G.neighborFinset u ∩ A' ⊆ B₀ := by
        intro x hx
        simp only [mem_inter, mem_neighborFinset, A', mem_union] at hx
        rcases hx.2 with hxA | hxB₀
        · exact absurd hx.1 (hnoA x hxA)
        · exact hxB₀
      have hdegA' : degIn G A' u ≤ 2 := by
        calc
          degIn G A' u = (G.neighborFinset u ∩ A').card := rfl
          _ ≤ B₀.card := Finset.card_le_card hsub
          _ = 2 := hB₀_card
      exact (min_le_left _ _).trans (by omega)
  have htotal : ∑ u ∈ N, min (degIn G A' u + 1) (degIn G B' u) ≤ 3 * (13 - T.card) := by
    have hT_sub : T ⊆ N := Finset.filter_subset _ _
    have hdisjT : Disjoint T (N \ T) := Finset.disjoint_sdiff
    have hunionT : T ∪ (N \ T) = N := Finset.union_sdiff_of_subset hT_sub
    rw [← hunionT, Finset.sum_union hdisjT]
    have hsumT : ∑ u ∈ T, min (degIn G A' u + 1) (degIn G B' u) = 0 :=
      Finset.sum_eq_zero hcost_T
    have hsumRest : ∑ u ∈ N \ T, min (degIn G A' u + 1) (degIn G B' u) ≤ 3 * (N \ T).card := by
      calc
        ∑ u ∈ N \ T, min (degIn G A' u + 1) (degIn G B' u)
            ≤ ∑ _u ∈ N \ T, 3 := Finset.sum_le_sum fun u hu => hcost_other u (sdiff_subset hu)
        _ = 3 * (N \ T).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hsumT, zero_add]
    rw [Finset.card_sdiff_of_subset hT_sub, hN_card] at hsumRest
    exact hsumRest
  refine ⟨S₄, ?_⟩
  rw [hcut, hEB']
  omega

private lemma H2_classical (G : SimpleGraph V) (hG : G.CliqueFree 3) (v : V)
    (hN_card : (G.neighborFinset v).card = 13)
    (hnbhd : 25 < mono G (G.neighborFinset v))
    (hbip : (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set V)).IsBipartite) :
    ∃ S : Finset V, mono G S ≤ 25 := by
  have hvN : v ∉ G.neighborFinset v := fun h =>
    G.loopless.irrefl v ((mem_neighborFinset G v v).mp h)
  set M : Finset V := (insert v (G.neighborFinset v))ᶜ
  have hM_card : M.card = 11 := by
    have h1 : (insert v (G.neighborFinset v)).card = 14 := by
      rw [Finset.card_insert_of_notMem hvN, hN_card]
    have h2 : M.card + (insert v (G.neighborFinset v)).card = 25 := by
      simpa [M] using Finset.card_compl_add_card (insert v (G.neighborFinset v))
    omega
  have hM_edges : 26 ≤ edgesIn G M := by
    have h2 := mono_nbhd_eq_edgesIn hG v
    change mono G (G.neighborFinset v) = edgesIn G M at h2
    omega
  obtain ⟨c⟩ := hbip
  let A₀_raw : Finset V := M.filter (fun x => if hx : x ∈ M then c ⟨x, hx⟩ = 0 else False)
  let B₀_raw : Finset V := M.filter (fun x => if hx : x ∈ M then c ⟨x, hx⟩ = 1 else False)
  have hdisj_raw : Disjoint A₀_raw B₀_raw := by
    rw [Finset.disjoint_left]
    intro x hA hB
    simp only [A₀_raw, B₀_raw, mem_filter] at hA hB
    rw [dif_pos hA.1] at hA
    rw [dif_pos hB.1] at hB
    exact Fin.zero_ne_one (hA.2.symm.trans hB.2)
  have hunion_raw : A₀_raw ∪ B₀_raw = M := by
    ext x
    simp only [A₀_raw, B₀_raw, mem_union, mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      have hfin : c ⟨x, hx⟩ = 0 ∨ c ⟨x, hx⟩ = 1 := by
        generalize hval : c ⟨x, hx⟩ = k
        fin_cases k <;> simp
      rcases hfin with h0 | h1
      · left; exact ⟨hx, by rw [dif_pos hx]; exact h0⟩
      · right; exact ⟨hx, by rw [dif_pos hx]; exact h1⟩
  have hind_A_raw : ∀ a ∈ A₀_raw, ∀ b ∈ A₀_raw, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [A₀_raw, mem_filter] at ha hb
    rw [dif_pos ha.1] at ha
    rw [dif_pos hb.1] at hb
    exact c.valid (show (G.induce (↑M : Set V)).Adj ⟨a, ha.1⟩ ⟨b, hb.1⟩ from hab)
      (ha.2.trans hb.2.symm)
  have hind_B_raw : ∀ a ∈ B₀_raw, ∀ b ∈ B₀_raw, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [B₀_raw, mem_filter] at ha hb
    rw [dif_pos ha.1] at ha
    rw [dif_pos hb.1] at hb
    exact c.valid (show (G.induce (↑M : Set V)).Adj ⟨a, ha.1⟩ ⟨b, hb.1⟩ from hab)
      (ha.2.trans hb.2.symm)
  obtain ⟨A, B, hAB_disj, hAB_union, hA_ind, hB_ind, hAB_le⟩ :
      ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = M ∧
        (∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) ∧ (∀ a ∈ B, ∀ b ∈ B, ¬ G.Adj a b) ∧
        A.card ≤ B.card := by
    rcases le_total A₀_raw.card B₀_raw.card with h | h
    · exact ⟨A₀_raw, B₀_raw, hdisj_raw, hunion_raw, hind_A_raw, hind_B_raw, h⟩
    · exact ⟨B₀_raw, A₀_raw, hdisj_raw.symm, by rw [Finset.union_comm, hunion_raw],
        hind_B_raw, hind_A_raw, h⟩
  have hAB_sum : A.card + B.card = 11 := by
    rw [← Finset.card_union_of_disjoint hAB_disj, hAB_union, hM_card]
  have hAB_prod_le : A.card * B.card ≤ 30 := by nlinarith
  have hdeg_mul : ∀ u : V, degIn G A u * degIn G B u ≤ 4 := by
    intro u
    have h := mul_deg_add_edges_le hG hAB_disj hA_ind hB_ind u
    rw [hAB_union] at h
    omega
  by_cases hT : ((G.neighborFinset v).filter (fun u => degIn G A u = 2 ∧ degIn G B u = 2)).card ≤ 6
  · exact case_small_T hG v hN_card hAB_disj hAB_union hA_ind hB_ind hdeg_mul hT
  · exact case_large_T hG v hN_card hAB_disj hAB_union hA_ind hB_ind hAB_sum hAB_le
      (by rwa [hAB_union]) (by omega)

theorem H2_proof : OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1.H2 := by
  intro G _ hG _ v hv hnbhd hbip
  have hN_eq' : G.neighborFinset v =
      @SimpleGraph.neighborFinset V G v
        (@Subtype.fintype V (Membership.mem (G.neighborSet v))
          (fun a => @neighborSet.memDecidable V G v (fun x y => Classical.propDecidable (G.Adj x y)) a)
          (Fin.fintype 25)) := by
    ext x
    simp only [mem_neighborFinset]
  have hmono_bridge : ∀ S : Finset V,
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card = mono G S := by
    intro S
    unfold mono
    congr 1
    ext e
    simp only [mem_filter, mem_edgeFinset]
  have hN_card : (@SimpleGraph.neighborFinset V G v
      (@Subtype.fintype V (Membership.mem (G.neighborSet v))
        (fun a => @neighborSet.memDecidable V G v (fun x y => Classical.propDecidable (G.Adj x y)) a)
        (Fin.fintype 25))).card = 13 := by
    rw [← hN_eq', SimpleGraph.card_neighborFinset_eq_degree, hv]
  have hnbhd' : 25 < mono G (@SimpleGraph.neighborFinset V G v
      (@Subtype.fintype V (Membership.mem (G.neighborSet v))
        (fun a => @neighborSet.memDecidable V G v (fun x y => Classical.propDecidable (G.Adj x y)) a)
        (Fin.fintype 25))) := by
    rw [← hN_eq', ← hmono_bridge]
    exact hnbhd
  have hbip' : (G.induce (↑((insert v (@SimpleGraph.neighborFinset V G v
      (@Subtype.fintype V (Membership.mem (G.neighborSet v))
        (fun a => @neighborSet.memDecidable V G v (fun x y => Classical.propDecidable (G.Adj x y)) a)
        (Fin.fintype 25))))ᶜ) : Set V)).IsBipartite := by
    rw [← hN_eq']
    exact hbip
  obtain ⟨S, hS⟩ := H2_classical G hG v hN_card hnbhd' hbip'
  exact ⟨S, by rw [hmono_bridge S]; exact hS⟩

end Erdos23H2R1H2Proof

theorem OMA.solution : OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1.H2 :=
  Erdos23H2R1H2Proof.H2_proof
