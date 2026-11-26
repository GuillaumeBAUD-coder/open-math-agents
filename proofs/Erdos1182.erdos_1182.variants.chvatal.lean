import FormalConjectures.ErdosProblems.«1182»
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic

/-!
Chvatal: for a tree on n vertices the Ramsey number against a triangle is 2 * n - 1.
-/

open SimpleGraph Function

/- Red cut between two blocks of size `n - 1` on `(2 * n - 1) - 1` vertices. -/
def crossAdj (n : ℕ) : SimpleGraph (Fin ((2 * n - 1) - 1)) :=
  SimpleGraph.fromRel fun x y => x.val < n - 1 ∧ n - 1 ≤ y.val

lemma crossAdj_adj {n : ℕ} {x y : Fin ((2 * n - 1) - 1)} :
    (crossAdj n).Adj x y ↔
      (x.val < n - 1 ∧ n - 1 ≤ y.val) ∨ (y.val < n - 1 ∧ n - 1 ≤ x.val) := by
  simp only [crossAdj, fromRel_adj]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · omega
    · omega

lemma crossAdj_compl_same {n : ℕ} {x y : Fin ((2 * n - 1) - 1)}
    (h : (crossAdj n)ᶜ.Adj x y) : x.val < n - 1 ↔ y.val < n - 1 := by
  rw [compl_adj] at h
  obtain ⟨_, hnot⟩ := h
  rw [crossAdj_adj] at hnot
  by_cases hx : x.val < n - 1
  · have hy : y.val < n - 1 := by
      by_contra hy
      exact hnot (Or.inl ⟨hx, Nat.le_of_not_lt hy⟩)
    exact iff_of_true hx hy
  · have hy : ¬ y.val < n - 1 := by
      by_contra hy
      exact hnot (Or.inr ⟨hy, Nat.le_of_not_lt hx⟩)
    exact iff_of_false hx hy

lemma crossAdj_walk_same {n : ℕ} {x y : Fin ((2 * n - 1) - 1)}
    (p : (crossAdj n)ᶜ.Walk x y) : x.val < n - 1 ↔ y.val < n - 1 := by
  induction p with
  | nil => rfl
  | cons h q ih => exact (crossAdj_compl_same h).trans ih

def lowEquiv (n : ℕ) (hn : 1 ≤ n) :
    Fin (n - 1) ≃ {x : Fin ((2 * n - 1) - 1) // x.val < n - 1} where
  toFun i :=
    ⟨⟨i.val, by have hi := i.isLt; omega⟩, by simp [i.isLt]⟩
  invFun x := ⟨x.1.val, by simp [x.2]⟩
  left_inv i := by ext; rfl
  right_inv x := by ext; rfl

lemma card_low (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {x : Fin ((2 * n - 1) - 1) // x.val < n - 1} = n - 1 := by
  rw [← Fintype.card_congr (lowEquiv n hn), Fintype.card_fin]

lemma card_high (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {x : Fin ((2 * n - 1) - 1) // ¬ x.val < n - 1} = n - 1 := by
  have hsub := Fintype.card_subtype_compl (fun x : Fin ((2 * n - 1) - 1) => x.val < n - 1)
  rw [hsub, card_low n hn, Fintype.card_fin]
  omega

lemma cross_sides {n : ℕ} {x y : Fin ((2 * n - 1) - 1)} (h : (crossAdj n).Adj x y) :
    (x.val < n - 1) ↔ ¬ y.val < n - 1 := by
  have h' := (crossAdj_adj).mp h
  rcases h' with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · constructor
    · intro _
      exact Nat.not_lt.mpr hy
    · intro _
      exact hx
  · constructor
    · intro hxlt
      omega
    · intro hnot
      exact False.elim (hnot hy)

lemma no_K3 {n : ℕ} :
    ¬ (⊤ : SimpleGraph (Fin 3)).IsContained (crossAdj n) := by
  intro ⟨f⟩
  have h01 := cross_sides (f.toHom.map_adj (by simp [top_adj] : (⊤ : SimpleGraph (Fin 3)).Adj 0 1))
  have h02 := cross_sides (f.toHom.map_adj (by simp [top_adj] : (⊤ : SimpleGraph (Fin 3)).Adj 0 2))
  have h12 := cross_sides (f.toHom.map_adj (by simp [top_adj] : (⊤ : SimpleGraph (Fin 3)).Adj 1 2))
  by_cases h0 : (f 0).val < n - 1
  · exact (h01.mp h0) (h12.mpr (h02.mp h0))
  · have h1 : (f 1).val < n - 1 := by
      by_contra h1
      exact h0 (h01.mpr h1)
    have h2 : (f 2).val < n - 1 := by
      by_contra h2
      exact h0 (h02.mpr h2)
    exact (h12.mp h1) h2

lemma no_tree_copy {α : Type} [Fintype α] {n : ℕ} (T : SimpleGraph α) (hT : T.IsTree)
    (hn : Fintype.card α = n) (hn1 : 1 ≤ n) :
    ¬ T.IsContained (crossAdj n)ᶜ := by
  intro ⟨f⟩
  obtain ⟨a0⟩ := hT.connected.nonempty
  have hside : ∀ b, (f a0).val < n - 1 ↔ (f b).val < n - 1 := by
    intro b
    obtain ⟨p⟩ := hT.connected a0 b
    exact crossAdj_walk_same (p.map f.toHom)
  by_cases h0 : (f a0).val < n - 1
  · let g : α → {x : Fin ((2 * n - 1) - 1) // x.val < n - 1} :=
      fun b => ⟨f b, (hside b).mp h0⟩
    have hginj : Injective g := by
      intro a b h
      apply f.injective
      exact congrArg Subtype.val h
    have hle := Fintype.card_le_of_injective g hginj
    rw [hn, card_low n hn1] at hle
    omega
  · let g : α → {x : Fin ((2 * n - 1) - 1) // ¬ x.val < n - 1} :=
      fun b => ⟨f b, fun hb => h0 ((hside b).mpr hb)⟩
    have hginj : Injective g := by
      intro a b h
      apply f.injective
      exact congrArg Subtype.val h
    have hle := Fintype.card_le_of_injective g hginj
    rw [hn, card_high n hn1] at hle
    omega

lemma compl_comap_eq {V W : Type} (e : V ↪ W) (G : SimpleGraph W) :
    (G.comap e)ᶜ = Gᶜ.comap e := by
  ext a b
  simp only [compl_adj, comap_adj]
  constructor
  · intro h
    exact ⟨e.injective.ne h.1, h.2⟩
  · intro h
    exact ⟨fun heq => h.1 (congrArg e heq), h.2⟩

lemma contained_comap {α β γ : Type} {H : SimpleGraph α} {G : SimpleGraph γ}
    (e : β ↪ γ) (h : H.IsContained (G.comap e)) : H.IsContained G :=
  h.trans ⟨(Embedding.comap e G).toCopy⟩

lemma forces_upward {β : Type} [Fintype β] (H : SimpleGraph β) {m m' : ℕ} (hm : m ≤ m')
    (h : ∀ C : SimpleGraph (Fin m),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ H.IsContained Cᶜ) :
    ∀ C : SimpleGraph (Fin m'),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ H.IsContained Cᶜ := by
  intro C
  let e := Fin.castLEEmb hm
  rcases h (C.comap e) with hK | hH
  · exact Or.inl (contained_comap e hK)
  · rw [compl_comap_eq e C] at hH
    exact Or.inr (contained_comap e hH)

lemma graphRamsey_of_threshold {β : Type} [Fintype β] (H : SimpleGraph β) {N : ℕ}
    (hforce : ∀ C : SimpleGraph (Fin N),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ H.IsContained Cᶜ)
    (hbad : ∃ C : SimpleGraph (Fin (N - 1)),
      ¬ (⊤ : SimpleGraph (Fin 3)).IsContained C ∧ ¬ H.IsContained Cᶜ) :
    graphRamsey (⊤ : SimpleGraph (Fin 3)) H = N := by
  let K : SimpleGraph (Fin 3) := ⊤
  let S : Set ℕ := {k | ∀ C : SimpleGraph (Fin k), K.IsContained C ∨ H.IsContained Cᶜ}
  change sInf S = N
  have hmem : N ∈ S := hforce
  have hnot : N - 1 ∉ S := by
    intro hS
    obtain ⟨C, hC1, hC2⟩ := hbad
    exact hC1 ((hS C).resolve_right hC2)
  have hne : S.Nonempty := ⟨N, hmem⟩
  apply le_antisymm
  · exact csInf_le' hmem
  · rw [le_csInf_iff'' hne]
    intro a ha
    by_contra hlt
    have ha' : a ≤ N - 1 := Nat.le_sub_one_of_lt (lt_of_not_ge hlt)
    have : N - 1 ∈ S := forces_upward H ha' ha
    exact hnot this

lemma contained_of_clique {α β : Type} [Fintype α] [Fintype β] (T : SimpleGraph α)
    (B : SimpleGraph β) {s : Set β} [Fintype s] (hcl : B.IsClique s)
    (hcard : Fintype.card α ≤ Fintype.card s) : T.IsContained B := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨Hom.toCopy ⟨fun a => (e a).1, ?_⟩ ?_⟩
  · intro a b hab
    exact hcl (e a).2 (e b).2
      (Subtype.coe_ne_coe.mpr (e.injective.ne (T.ne_of_adj hab)))
  · intro a b h
    exact e.injective (Subtype.ext h)

lemma extend_leaf {α β : Type} [DecidableEq α] {T : SimpleGraph α} {B : SimpleGraph β} {v u : α}
    (hu : u ≠ v) (_hvu : T.Adj v u) (huniq : ∀ w, T.Adj v w → w = u)
    (f : Copy (T.induce ({v}ᶜ : Set α)) B) (w : β)
    (hw : w ∉ Set.range (⇑f.toHom)) (hwadj : B.Adj w (f ⟨u, hu⟩)) :
    T.IsContained B := by
  let φ : α → β := fun x => if h : x = v then w else f.toHom ⟨x, h⟩
  have hφv : φ v = w := dif_pos rfl
  have hφu : φ u = f ⟨u, hu⟩ := dif_neg hu
  have hφne : ∀ x (hx : x ≠ v), φ x = f.toHom ⟨x, hx⟩ := fun _ hx => dif_neg hx
  have hmap : ∀ {a b : α}, T.Adj a b → B.Adj (φ a) (φ b) := by
    intro a b hab
    by_cases ha : a = v
    · have hb : b = u := huniq b (ha ▸ hab)
      rw [ha, hb, hφv, hφu]
      exact hwadj
    · by_cases hb : b = v
      · have hau : a = u := huniq a (hb ▸ hab.symm)
        rw [hau, hb, hφu, hφv]
        exact hwadj.symm
      · rw [hφne a ha, hφne b hb]
        exact f.toHom.map_adj hab
  have hinj : Injective φ := by
    intro a b hab
    by_cases ha : a = v
    · by_cases hb : b = v
      · exact ha.trans hb.symm
      · have hfw : w = f.toHom ⟨b, hb⟩ :=
          hφv.symm.trans (congrArg φ ha.symm) |>.trans hab |>.trans (hφne b hb)
        exact (hw ⟨⟨b, hb⟩, hfw.symm⟩).elim
    · by_cases hb : b = v
      · have hfw : f.toHom ⟨a, ha⟩ = w :=
          (hφne a ha).symm.trans hab |>.trans (congrArg φ hb) |>.trans hφv
        exact (hw ⟨⟨a, ha⟩, hfw⟩).elim
      · have hfab : f.toHom ⟨a, ha⟩ = f.toHom ⟨b, hb⟩ :=
          (hφne a ha).symm.trans hab |>.trans (hφne b hb)
        exact congrArg Subtype.val (f.injective hfab)
  exact ⟨Hom.toCopy ⟨φ, hmap⟩ hinj⟩

lemma forces_chvatal (n : ℕ) :
    ∀ (α : Type) [Fintype α] (T : SimpleGraph α),
      T.IsTree → Fintype.card α = n →
      ∀ C : SimpleGraph (Fin (2 * n - 1)),
        (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ T.IsContained Cᶜ := by
  induction n using Nat.strongRecOn with | ind n ih =>
  intro α _ T hT hn C
  by_cases hn0 : n = 0
  · have : Nonempty α := hT.connected.nonempty
    have : 0 < Fintype.card α := Fintype.card_pos
    omega
  · by_cases hn1 : n = 1
    · have hsub : Subsingleton α :=
        (Fintype.card_le_one_iff_subsingleton).mp (by rw [hn]; omega)
      have hbot : T = ⊥ := by
        ext a b
        constructor
        · intro hab
          exact (T.ne_of_adj hab (Subsingleton.elim a b)).elim
        · simp
      subst hbot
      right
      exact (bot_isContained_iff_card_le).mpr (by simp [hn, hn1])
    · have hn2 : 2 ≤ n := by omega
      haveI := Classical.decEq α
      haveI := Classical.decRel T.Adj
      haveI : Nontrivial α :=
        (Fintype.one_lt_card_iff_nontrivial).mp (by rw [hn]; omega)
      obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hvu, huniq⟩ := (degree_eq_one_iff_existsUnique_adj).mp hv
      have hu : u ≠ v := (T.ne_of_adj hvu).symm
      have hconn := hT.connected.induce_compl_singleton_of_degree_eq_one hv
      have hacy := hT.isAcyclic.induce ({v}ᶜ : Set α)
      have hT' : (T.induce (({v} : Set α)ᶜ)).IsTree := ⟨hconn, hacy⟩
      have hcard' : Fintype.card ↥(({v} : Set α)ᶜ) = n - 1 := by
        rw [← hn]
        simpa using Set.card_ne_eq v
      have hlt : n - 1 < n := by omega
      have hle : 2 * (n - 1) - 1 ≤ 2 * n - 1 := by omega
      let e := Fin.castLEEmb hle
      have hsmall :=
        ih (n - 1) hlt (↥(({v} : Set α)ᶜ)) (T.induce (({v} : Set α)ᶜ)) hT' hcard' (C.comap e)
      by_cases htri : (⊤ : SimpleGraph (Fin 3)).IsContained C
      · exact Or.inl htri
      · rcases hsmall with hK | hTcopy
        · exact (htri (contained_comap e hK)).elim
        · rw [compl_comap_eq e C] at hTcopy
          obtain ⟨f⟩ := contained_comap e hTcopy
          let y : Fin (2 * n - 1) := f ⟨u, hu⟩
          let img : Finset (Fin (2 * n - 1)) := Finset.univ.map f.toEmbedding
          have himg : Finset.card img = n - 1 := by
            rw [Finset.card_map, Finset.card_univ, hcard']
          have hout : Finset.card imgᶜ = n := by
            rw [Finset.card_compl, himg, Fintype.card_fin]
            omega
          by_cases hblue : ∃ w ∈ imgᶜ, Cᶜ.Adj w y
          · obtain ⟨w, hw, hwadj⟩ := hblue
            have hwrange : w ∉ Set.range (⇑f.toHom) := by
              intro ⟨z, hz⟩
              have hwimg : w ∈ img := by
                rw [Finset.mem_map]
                exact ⟨z, Finset.mem_univ z, by simpa [Copy.toEmbedding] using hz⟩
              exact (Finset.mem_compl.mp hw) hwimg
            have hy : y = f ⟨u, hu⟩ := rfl
            exact Or.inr (extend_leaf hu hvu huniq f w hwrange (hy ▸ hwadj))
          · push Not at hblue
            have hcf : C.CliqueFree 3 := by
              contrapose! htri
              exact (not_cliqueFree_iff_top_isContained 3).mp htri
            have hsub : (↑imgᶜ : Set (Fin (2 * n - 1))) ⊆ C.neighborSet y := by
              intro w hw
              have hwfin : w ∈ imgᶜ := by simpa using hw
              have hne : w ≠ y := by
                intro heq
                have hyimg : y ∈ img := by
                  rw [Finset.mem_map]
                  exact ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩
                exact (Finset.mem_compl.mp hwfin) (heq ▸ hyimg)
              have hnot : ¬ Cᶜ.Adj w y := hblue w hwfin
              rw [mem_neighborSet]
              rw [compl_adj] at hnot
              rcases not_and_or.mp hnot with h | h
              · exact (h hne).elim
              · exact (not_not.mp h).symm
            have hindep : C.IsIndepSet (↑imgᶜ : Set _) := by
              rw [isIndepSet_iff]
              exact Set.Pairwise.mono hsub
                ((isIndepSet_iff (G := C) (s := C.neighborSet y)).mp
                  (isIndepSet_neighborSet_of_triangleFree C hcf y))
            have hcl : Cᶜ.IsClique (↑imgᶜ : Set _) :=
              (isClique_compl (G := C) (s := (↑imgᶜ : Set _))).mpr hindep
            have hcard_out : Fintype.card ↥(imgᶜ) = n := (Fintype.card_coe (imgᶜ)).trans hout
            right
            exact contained_of_clique T Cᶜ hcl (le_of_eq (hn ▸ hcard_out.symm))

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.chvatal := by
  intro n T hT
  unfold Erdos1182.IsTriangleGood
  have hn1 : 1 ≤ n := by
    have : Nonempty (Fin n) := hT.connected.nonempty
    have : 0 < n := by
      simpa [Fintype.card_fin] using Fintype.card_pos_iff.mpr this
    omega
  exact graphRamsey_of_threshold T (N := 2 * n - 1)
    (forces_chvatal n (Fin n) T hT (Fintype.card_fin n))
    ⟨crossAdj n, no_K3, no_tree_copy T hT (Fintype.card_fin n) hn1⟩
