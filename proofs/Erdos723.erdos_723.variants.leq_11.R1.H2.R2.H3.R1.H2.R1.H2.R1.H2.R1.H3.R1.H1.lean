import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FinCases

-- The eight lines split into two concurrent fours. Their sixteen crossings are the
-- code columns, each line keeps six private columns, and forty-five columns stay empty.

noncomputable section

open Finset Classical

abbrev L723 := Fin 4 ⊕ Fin 4

abbrev Idx723 := ((Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (L723 × Fin 6))) ⊕ Fin 45

structure Geom where
  A : Fin 8 → Fin 111 → Bool
  S : Finset (Fin 111)
  p : Fin 111
  q : Fin 111
  cardS : S.card = 16
  hrow : ∀ a, (univ.filter fun x => A a x = true).card = 11
  hsec : ∀ a, (S.filter fun x => A a x = true).card = 4
  hdeg : ∀ x ∈ S, (univ.filter fun a => A a x = true).card = 2
  hpair : ∀ a b, a ≠ b → ∃! x, A a x = true ∧ A b x = true
  hp : p ∉ S
  hq : q ∉ S
  hpq : p ≠ q
  hfourP : (univ.filter fun a => A a p = true).card = 4
  hfourQ : (univ.filter fun a => A a q = true).card = 4
  hblock : ∀ a b, a ≠ b →
    ((∃ x ∉ S, A a x = true ∧ A b x = true) ↔
      (a ∈ univ.filter (fun t => A t p = true) ↔ b ∈ univ.filter (fun t => A t p = true)))

def blockP (G : Geom) : Finset (Fin 8) := univ.filter fun a => G.A a G.p = true

def blockQ (G : Geom) : Finset (Fin 8) := univ.filter fun a => G.A a G.q = true

@[simp] lemma mem_blockP (G : Geom) (a : Fin 8) : a ∈ blockP G ↔ G.A a G.p = true := by
  simp [blockP]

@[simp] lemma mem_blockQ (G : Geom) (a : Fin 8) : a ∈ blockQ G ↔ G.A a G.q = true := by
  simp [blockQ]

lemma card_blockP (G : Geom) : (blockP G).card = 4 := G.hfourP

lemma card_blockQ (G : Geom) : (blockQ G).card = 4 := G.hfourQ

noncomputable def meet (G : Geom) (a b : Fin 8) (h : a ≠ b) : Fin 111 :=
  Classical.choose (G.hpair a b h)

lemma meet_spec (G : Geom) (a b : Fin 8) (h : a ≠ b) :
    G.A a (meet G a b h) = true ∧ G.A b (meet G a b h) = true ∧
      ∀ y, G.A a y = true ∧ G.A b y = true → y = meet G a b h := by
  have spec := Classical.choose_spec (G.hpair a b h)
  exact ⟨spec.1.1, spec.1.2, spec.2⟩

lemma disjoint_blocks (G : Geom) : Disjoint (blockP G) (blockQ G) := by
  rw [disjoint_left]
  intro a haP haQ
  have sub : blockQ G ⊆ blockP G := by
    intro b hbQ
    by_contra hbP
    have hne : a ≠ b := by
      intro h
      exact hbP (h ▸ haP)
    have hno : ¬ ∃ x ∉ G.S, G.A a x = true ∧ G.A b x = true := by
      intro hex
      have hiff := (G.hblock a b hne).mp hex
      have haF : a ∈ univ.filter fun t => G.A t G.p = true := by simpa [blockP] using haP
      exact hbP (by simpa [blockP] using hiff.mp haF)
    exact hno ⟨G.q, G.hq, (mem_blockQ G a).mp haQ, (mem_blockQ G b).mp hbQ⟩
  have heq : blockQ G = blockP G :=
    eq_of_subset_of_card_le sub (by rw [card_blockP, card_blockQ])
  have hcard : ((blockP G).erase a).card = 3 := by
    rw [card_erase_of_mem haP, card_blockP]
  have hneEmpty : ((blockP G).erase a).Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨b, hb⟩ := hneEmpty
  have hbP : b ∈ blockP G := (mem_erase.mp hb).2
  have hba : b ≠ a := (mem_erase.mp hb).1
  have hba' : a ≠ b := hba.symm
  have hbQ : b ∈ blockQ G := by rw [heq]; exact hbP
  have spec := meet_spec G a b hba'
  have hpmeet : G.p = meet G a b hba' :=
    spec.2.2 G.p ⟨(mem_blockP G a).mp haP, (mem_blockP G b).mp hbP⟩
  have hqmeet : G.q = meet G a b hba' :=
    spec.2.2 G.q ⟨(mem_blockQ G a).mp haQ, (mem_blockQ G b).mp hbQ⟩
  exact G.hpq (hpmeet.trans hqmeet.symm)

lemma blockQ_eq_compl (G : Geom) : blockQ G = univ \ blockP G := by
  refine eq_of_subset_of_card_le ?_ ?_
  · intro b hb
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hbP
    exact (disjoint_left.mp (disjoint_blocks G)) hbP hb
  · rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_blockP, card_blockQ]

lemma not_blockP_of_blockQ (G : Geom) {a : Fin 8} (ha : a ∈ blockQ G) : a ∉ blockP G := by
  intro hp
  exact (disjoint_left.mp (disjoint_blocks G)) hp ha

lemma not_blockQ_of_blockP (G : Geom) {a : Fin 8} (ha : a ∈ blockP G) : a ∉ blockQ G := by
  intro hq
  exact (disjoint_left.mp (disjoint_blocks G)) ha hq

noncomputable def slotEquiv {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) {n : ℕ} (h : s.card = n) : Fin n ≃ {x // x ∈ s} :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, h])).symm

noncomputable def slot {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) {n : ℕ} (h : s.card = n) (i : Fin n) : α :=
  (slotEquiv s h i).1

lemma slot_mem {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) {n : ℕ} (h : s.card = n) (i : Fin n) : slot s h i ∈ s :=
  (slotEquiv s h i).2

lemma slot_inj {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) {n : ℕ} (h : s.card = n) : Function.Injective (slot s h) := by
  intro i j hij
  apply (slotEquiv s h).injective
  exact Subtype.ext hij

noncomputable def lineP (G : Geom) (a : Fin 4) : Fin 8 :=
  slot (blockP G) (card_blockP G) a

noncomputable def lineQ (G : Geom) (b : Fin 4) : Fin 8 :=
  slot (blockQ G) (card_blockQ G) b

lemma lineP_mem (G : Geom) (a : Fin 4) : lineP G a ∈ blockP G :=
  slot_mem _ _ _

lemma lineQ_mem (G : Geom) (b : Fin 4) : lineQ G b ∈ blockQ G :=
  slot_mem _ _ _

lemma lineP_inj (G : Geom) : Function.Injective (lineP G) :=
  slot_inj _ _

lemma lineQ_inj (G : Geom) : Function.Injective (lineQ G) :=
  slot_inj _ _

lemma lineP_ne_lineQ (G : Geom) (a b : Fin 4) : lineP G a ≠ lineQ G b := by
  intro h
  exact not_blockQ_of_blockP G (lineP_mem G a) (by rw [h]; exact lineQ_mem G b)

lemma lineP_on_p (G : Geom) (a : Fin 4) : G.A (lineP G a) G.p = true :=
  (mem_blockP G _).mp (lineP_mem G a)

lemma lineQ_on_q (G : Geom) (b : Fin 4) : G.A (lineQ G b) G.q = true :=
  (mem_blockQ G _).mp (lineQ_mem G b)

lemma lineP_off_q (G : Geom) (a : Fin 4) : G.A (lineP G a) G.q = false := by
  have hnot : lineP G a ∉ blockQ G := not_blockQ_of_blockP G (lineP_mem G a)
  simpa [mem_blockQ] using hnot

lemma lineQ_off_p (G : Geom) (b : Fin 4) : G.A (lineQ G b) G.p = false := by
  have hnot : lineQ G b ∉ blockP G := not_blockP_of_blockQ G (lineQ_mem G b)
  simpa [mem_blockP] using hnot

def lineMap (G : Geom) : L723 → Fin 8
  | .inl a => lineP G a
  | .inr b => lineQ G b

lemma lineMap_inj (G : Geom) : Function.Injective (lineMap G) := by
  intro x y hxy
  match x, y with
  | .inl a, .inl a' =>
      obtain rfl := lineP_inj G hxy
      rfl
  | .inr b, .inr b' =>
      obtain rfl := lineQ_inj G hxy
      rfl
  | .inl a, .inr b =>
      exact (lineP_ne_lineQ G a b hxy).elim
  | .inr b, .inl a =>
      exact (lineP_ne_lineQ G a b hxy.symm).elim

lemma card_L723 : Fintype.card L723 = 8 := by
  simp [Fintype.card_sum, Fintype.card_fin]

lemma lineMap_bij (G : Geom) : Function.Bijective (lineMap G) := by
  refine ⟨lineMap_inj G, ?_⟩
  intro y
  let e : L723 ≃ Fin 8 :=
    Fintype.equivFinOfCardEq (card_L723.trans (Fintype.card_fin (n := 8)).symm)
  have hinj : Function.Injective (lineMap G ∘ e.symm) := (lineMap_inj G).comp e.symm.injective
  obtain ⟨i, hi⟩ := (Function.Injective.bijective_of_finite hinj).2 y
  exact ⟨e.symm i, hi⟩

noncomputable def lineEquiv (G : Geom) : L723 ≃ Fin 8 :=
  Equiv.ofBijective (lineMap G) (lineMap_bij G)

noncomputable def codePoint (G : Geom) (a b : Fin 4) : Fin 111 :=
  meet G (lineP G a) (lineQ G b) (lineP_ne_lineQ G a b)

lemma codePoint_spec (G : Geom) (a b : Fin 4) :
    G.A (lineP G a) (codePoint G a b) = true ∧ G.A (lineQ G b) (codePoint G a b) = true ∧
      ∀ y, G.A (lineP G a) y = true ∧ G.A (lineQ G b) y = true → y = codePoint G a b :=
  meet_spec G _ _ _

lemma codePoint_mem (G : Geom) (a b : Fin 4) : codePoint G a b ∈ G.S := by
  by_contra hnot
  have spec := codePoint_spec G a b
  have hex : ∃ x ∉ G.S, G.A (lineP G a) x = true ∧ G.A (lineQ G b) x = true :=
    ⟨codePoint G a b, hnot, spec.1, spec.2.1⟩
  have hiff := (G.hblock _ _ (lineP_ne_lineQ G a b)).mp hex
  exact not_blockP_of_blockQ G (lineQ_mem G b) (hiff.mp (lineP_mem G a))

lemma meet_sameP (G : Geom) (a b : Fin 4) (hne : a ≠ b) :
    meet G (lineP G a) (lineP G b) ((lineP_inj G).ne hne) = G.p := by
  have spec := meet_spec G (lineP G a) (lineP G b) ((lineP_inj G).ne hne)
  exact (spec.2.2 G.p ⟨lineP_on_p G a, lineP_on_p G b⟩).symm

lemma meet_sameQ (G : Geom) (a b : Fin 4) (hne : a ≠ b) :
    meet G (lineQ G a) (lineQ G b) ((lineQ_inj G).ne hne) = G.q := by
  have spec := meet_spec G (lineQ G a) (lineQ G b) ((lineQ_inj G).ne hne)
  exact (spec.2.2 G.q ⟨lineQ_on_q G a, lineQ_on_q G b⟩).symm

lemma lines_at_code (G : Geom) (a b : Fin 4) (t : Fin 8) :
    G.A t (codePoint G a b) = true ↔ t = lineP G a ∨ t = lineQ G b := by
  let here : Finset (Fin 8) := univ.filter fun u => G.A u (codePoint G a b) = true
  have hsub : ({lineP G a, lineQ G b} : Finset (Fin 8)) ⊆ here := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _, (codePoint_spec G a b).1⟩
    · exact mem_filter.mpr ⟨mem_univ _, (codePoint_spec G a b).2.1⟩
  have hhere : here.card = 2 := G.hdeg _ (codePoint_mem G a b)
  have hpair : ({lineP G a, lineQ G b} : Finset (Fin 8)).card = 2 :=
    (card_pair_eq_two_iff).mpr (lineP_ne_lineQ G a b)
  have heq : ({lineP G a, lineQ G b} : Finset (Fin 8)) = here :=
    eq_of_subset_of_card_le hsub (by rw [hhere, hpair])
  have ht : t ∈ here ↔ G.A t (codePoint G a b) = true := by simp [here]
  rw [← ht, ← heq]
  simp [mem_insert, mem_singleton]

def codesOn (G : Geom) : L723 → Finset (Fin 111)
  | .inl a => univ.image fun j : Fin 4 => codePoint G a j
  | .inr b => univ.image fun j : Fin 4 => codePoint G j b

lemma codesOn_card (G : Geom) (a : L723) : (codesOn G a).card = 4 := by
  match a with
  | .inl a =>
      rw [codesOn, card_image_of_injective _ (fun j k h => ?_), card_univ]
      simp [Fintype.card_fin]
      have hon : G.A (lineQ G j) (codePoint G a k) = true := by
        rw [← h]
        exact (codePoint_spec G a j).2.1
      rcases (lines_at_code G a k (lineQ G j)).mp hon with h1 | h1
      · exact (lineP_ne_lineQ G a j h1.symm).elim
      · exact lineQ_inj G h1
  | .inr b =>
      rw [codesOn, card_image_of_injective _ (fun j k h => ?_), card_univ]
      simp [Fintype.card_fin]
      have hon : G.A (lineP G j) (codePoint G k b) = true := by
        rw [← h]
        exact (codePoint_spec G j b).1
      rcases (lines_at_code G k b (lineP G j)).mp hon with h1 | h1
      · exact lineP_inj G h1
      · exact (lineP_ne_lineQ G j b h1).elim

lemma codesOn_subset_support (G : Geom) (a : L723) :
    codesOn G a ⊆ univ.filter fun x => G.A (lineMap G a) x = true := by
  match a with
  | .inl a =>
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_univ _, (codePoint_spec G a j).1⟩
  | .inr b =>
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_univ _, (codePoint_spec G j b).2.1⟩

lemma codesOn_subset_S (G : Geom) (a : L723) : codesOn G a ⊆ G.S := by
  match a with
  | .inl a =>
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact codePoint_mem G a j
  | .inr b =>
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact codePoint_mem G j b

def centerOf (G : Geom) : L723 → Fin 111
  | .inl _ => G.p
  | .inr _ => G.q

lemma center_on_line (G : Geom) (a : L723) :
    G.A (lineMap G a) (centerOf G a) = true := by
  match a with
  | .inl a => exact lineP_on_p G a
  | .inr b => exact lineQ_on_q G b

lemma center_not_S (G : Geom) (a : L723) : centerOf G a ∉ G.S := by
  match a with
  | .inl _ => exact G.hp
  | .inr _ => exact G.hq

lemma center_not_codes (G : Geom) (a : L723) : centerOf G a ∉ codesOn G a := by
  intro h
  exact center_not_S G a (codesOn_subset_S G a h)

def support (G : Geom) (a : L723) : Finset (Fin 111) :=
  univ.filter fun x => G.A (lineMap G a) x = true

lemma support_card (G : Geom) (a : L723) : (support G a).card = 11 := by
  simpa [support, lineMap] using G.hrow (lineMap G a)

def privSet (G : Geom) (a : L723) : Finset (Fin 111) :=
  support G a \ (codesOn G a ∪ {centerOf G a})

lemma priv_card (G : Geom) (a : L723) : (privSet G a).card = 6 := by
  have hsub : codesOn G a ∪ {centerOf G a} ⊆ support G a := by
    intro x hx
    simp only [mem_union, mem_singleton] at hx
    rcases hx with hx | rfl
    · exact codesOn_subset_support G a hx
    · exact mem_filter.mpr ⟨mem_univ _, center_on_line G a⟩
  have hdis : Disjoint (codesOn G a) ({centerOf G a} : Finset (Fin 111)) := by
    rw [disjoint_left]
    intro x hx hc
    simp only [mem_singleton] at hc
    rw [hc] at hx
    exact center_not_codes G a hx
  rw [privSet, card_sdiff_of_subset hsub, card_union_of_disjoint hdis, card_singleton,
    codesOn_card G a, support_card G a]

lemma priv_not_S (G : Geom) (a : L723) {x : Fin 111} (hx : x ∈ privSet G a) : x ∉ G.S := by
  intro hS
  have hxS : x ∈ support G a := (mem_sdiff.mp hx).1
  have hsec : x ∈ G.S.filter fun y => G.A (lineMap G a) y = true :=
    mem_filter.mpr ⟨hS, (mem_filter.mp hxS).2⟩
  have hcodes : codesOn G a = G.S.filter fun y => G.A (lineMap G a) y = true := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      have hyS := codesOn_subset_S G a hy
      have hyA := codesOn_subset_support G a hy
      exact mem_filter.mpr ⟨hyS, (mem_filter.mp hyA).2⟩
    · rw [codesOn_card, G.hsec]
  have hxcode : x ∈ codesOn G a := by rw [hcodes]; exact hsec
  exact (mem_sdiff.mp hx).2 (mem_union_left _ hxcode)

lemma priv_ne_center (G : Geom) (a : L723) {x : Fin 111} (hx : x ∈ privSet G a) :
    x ≠ centerOf G a := by
  intro h
  have hxC : x ∈ codesOn G a ∪ {centerOf G a} := by
    rw [h]
    exact mem_union_right _ (mem_singleton_self _)
  exact (mem_sdiff.mp hx).2 hxC

noncomputable def privFun (G : Geom) (t : L723 × Fin 6) : Fin 111 :=
  slot (privSet G t.1) (priv_card G t.1) t.2

lemma privFun_mem (G : Geom) (t : L723 × Fin 6) : privFun G t ∈ privSet G t.1 :=
  slot_mem _ _ _

lemma privFun_only (G : Geom) (a b : L723) (i : Fin 6) :
    G.A (lineMap G a) (privFun G (b, i)) = true ↔ a = b := by
  constructor
  · intro hA
    by_contra hne
    have hx := privFun_mem G (b, i)
    have hon : G.A (lineMap G b) (privFun G (b, i)) = true :=
      (mem_filter.mp ((mem_sdiff.mp hx).1)).2
    match a, b with
    | .inl a, .inl b =>
        have spec := meet_spec G (lineP G a) (lineP G b) ((lineP_inj G).ne (by
          intro hab
          exact hne (congrArg Sum.inl hab)))
        have hpriv := spec.2.2 (privFun G (.inl b, i)) ⟨hA, hon⟩
        have hpmeet := spec.2.2 G.p ⟨lineP_on_p G a, lineP_on_p G b⟩
        exact priv_ne_center G (.inl b) hx (hpriv.trans hpmeet.symm)
    | .inr a, .inr b =>
        have spec := meet_spec G (lineQ G a) (lineQ G b) ((lineQ_inj G).ne (by
          intro hab
          exact hne (congrArg Sum.inr hab)))
        have hpriv := spec.2.2 (privFun G (.inr b, i)) ⟨hA, hon⟩
        have hqmeet := spec.2.2 G.q ⟨lineQ_on_q G a, lineQ_on_q G b⟩
        exact priv_ne_center G (.inr b) hx (hpriv.trans hqmeet.symm)
    | .inl a, .inr b =>
        have hpriv := (codePoint_spec G a b).2.2 (privFun G (.inr b, i)) ⟨hA, hon⟩
        exact priv_not_S G (.inr b) hx (hpriv.symm ▸ codePoint_mem G a b)
    | .inr a, .inl b =>
        have hpriv := (codePoint_spec G b a).2.2 (privFun G (.inl b, i)) ⟨hon, hA⟩
        exact priv_not_S G (.inl b) hx (hpriv.symm ▸ codePoint_mem G b a)
  · intro hab
    rw [hab]
    exact (mem_filter.mp ((mem_sdiff.mp (privFun_mem G (b, i))).1)).2

lemma privFun_inj (G : Geom) : Function.Injective (privFun G) := by
  intro t s hts
  rcases t with ⟨b, i⟩
  rcases s with ⟨c, j⟩
  have hon : G.A (lineMap G b) (privFun G (b, i)) = true :=
    (mem_filter.mp ((mem_sdiff.mp (privFun_mem G (b, i))).1)).2
  have hbc : b = c := (privFun_only G b c j).mp (hts ▸ hon)
  subst hbc
  exact Prod.ext rfl (slot_inj _ _ (by simpa [privFun] using hts))

def codeImage (G : Geom) : Finset (Fin 111) :=
  univ.image fun t : Fin 4 × Fin 4 => codePoint G t.1 t.2

lemma codePoint_inj (G : Geom) : Function.Injective (fun t : Fin 4 × Fin 4 => codePoint G t.1 t.2) := by
  intro t s hts
  rcases t with ⟨a, b⟩
  rcases s with ⟨c, d⟩
  have heq : codePoint G a b = codePoint G c d := hts
  have honP : G.A (lineP G a) (codePoint G c d) = true := by rw [← heq]; exact (codePoint_spec G a b).1
  have honQ : G.A (lineQ G b) (codePoint G c d) = true := by rw [← heq]; exact (codePoint_spec G a b).2.1
  have hac : lineP G a = lineP G c := by
    rcases (lines_at_code G c d (lineP G a)).mp honP with h1 | h1
    · exact h1
    · exact (lineP_ne_lineQ G a d h1).elim
  have hbd : lineQ G b = lineQ G d := by
    rcases (lines_at_code G c d (lineQ G b)).mp honQ with h1 | h1
    · exact (lineP_ne_lineQ G c b h1.symm).elim
    · exact h1
  exact Prod.ext (lineP_inj G hac) (lineQ_inj G hbd)

lemma codeImage_card (G : Geom) : (codeImage G).card = 16 := by
  rw [codeImage, card_image_of_injective _ (codePoint_inj G), card_univ]
  simp [Fintype.card_prod, Fintype.card_fin]

lemma codeImage_eq_S (G : Geom) : codeImage G = G.S := by
  refine eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨t, -, rfl⟩ := mem_image.mp hx
    exact codePoint_mem G t.1 t.2
  · rw [codeImage_card, G.cardS]

noncomputable def privImage (G : Geom) : Finset (Fin 111) :=
  univ.image (privFun G)

lemma privImage_card (G : Geom) : (privImage G).card = 48 := by
  rw [privImage, card_image_of_injective _ (privFun_inj G), card_univ, Fintype.card_prod,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

lemma privImage_disj_S (G : Geom) : Disjoint (privImage G) G.S := by
  rw [disjoint_left]
  intro x hx hS
  obtain ⟨t, -, rfl⟩ := mem_image.mp hx
  exact priv_not_S G t.1 (privFun_mem G t) hS

lemma priv_ne_p (G : Geom) (t : L723 × Fin 6) : privFun G t ≠ G.p := by
  intro h
  have hx := privFun_mem G t
  match t with
  | ⟨.inl a, i⟩ => exact priv_ne_center G (.inl a) hx h
  | ⟨.inr b, i⟩ =>
      have hon : G.A (lineQ G b) (privFun G (⟨.inr b, i⟩)) = true :=
        (mem_filter.mp ((mem_sdiff.mp hx).1)).2
      rw [h] at hon
      exact Bool.noConfusion (hon.symm.trans (lineQ_off_p G b))

lemma priv_ne_q (G : Geom) (t : L723 × Fin 6) : privFun G t ≠ G.q := by
  intro h
  have hx := privFun_mem G t
  match t with
  | ⟨.inr b, i⟩ => exact priv_ne_center G (.inr b) hx h
  | ⟨.inl a, i⟩ =>
      have hon : G.A (lineP G a) (privFun G (⟨.inl a, i⟩)) = true :=
        (mem_filter.mp ((mem_sdiff.mp hx).1)).2
      rw [h] at hon
      exact Bool.noConfusion (hon.symm.trans (lineP_off_q G a))

def centers (G : Geom) : Finset (Fin 111) := {G.p, G.q}

lemma centers_card (G : Geom) : (centers G).card = 2 := by
  rw [centers, card_pair_eq_two_iff.mpr G.hpq]

lemma centers_disj_S (G : Geom) : Disjoint (centers G) G.S := by
  rw [disjoint_left]
  intro x hx hS
  simp only [centers, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact G.hp hS
  · exact G.hq hS

lemma privImage_disj_centers (G : Geom) : Disjoint (privImage G) (centers G) := by
  rw [disjoint_left]
  intro x hx hc
  obtain ⟨t, -, rfl⟩ := mem_image.mp hx
  simp only [centers, mem_insert, mem_singleton] at hc
  rcases hc with h | h
  · exact priv_ne_p G t h
  · exact priv_ne_q G t h

def covered (G : Geom) : Finset (Fin 111) :=
  (G.S ∪ centers G) ∪ privImage G

lemma covered_card (G : Geom) : (covered G).card = 66 := by
  have h1 : Disjoint G.S (centers G) := (centers_disj_S G).symm
  have h2 : Disjoint (G.S ∪ centers G) (privImage G) := by
    rw [disjoint_union_left]
    exact ⟨(privImage_disj_S G).symm, (privImage_disj_centers G).symm⟩
  rw [covered, card_union_of_disjoint h2, card_union_of_disjoint h1, G.cardS, centers_card,
    privImage_card]

def emptyCols (G : Geom) : Finset (Fin 111) :=
  univ \ covered G

lemma empty_card (G : Geom) : (emptyCols G).card = 45 := by
  rw [emptyCols, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, covered_card]

noncomputable def emptyFun (G : Geom) (t : Fin 45) : Fin 111 :=
  slot (emptyCols G) (empty_card G) t

lemma empty_off (G : Geom) (a : L723) (t : Fin 45) :
    G.A (lineMap G a) (emptyFun G t) = false := by
  have hempty : emptyFun G t ∉ covered G := (mem_sdiff.mp (slot_mem _ _ t)).2
  by_contra hA
  have hon : emptyFun G t ∈ support G a := mem_filter.mpr ⟨mem_univ _, by simpa using hA⟩
  have hsub : support G a ⊆ covered G := by
    intro x hx
    have hxA : G.A (lineMap G a) x = true := (mem_filter.mp hx).2
    by_cases hS : x ∈ G.S
    · exact mem_union_left _ (mem_union_left _ hS)
    · by_cases hcent : x = centerOf G a
      · match a with
        | .inl _ =>
            rw [hcent]
            exact mem_union_left _ (mem_union_right _ (by simp [centers, centerOf]))
        | .inr _ =>
            rw [hcent]
            exact mem_union_left _ (mem_union_right _ (by simp [centers, centerOf]))
      · have hpriv : x ∈ privSet G a := by
          refine mem_sdiff.mpr ⟨hx, ?_⟩
          intro hbad
          simp only [mem_union, mem_singleton] at hbad
          rcases hbad with hcode | hcenter
          · exact hS (codesOn_subset_S G a hcode)
          · exact hcent hcenter
        refine mem_union_right _ ?_
        refine mem_image.mpr ⟨⟨a, (slotEquiv (privSet G a) (priv_card G a)).symm ⟨x, hpriv⟩⟩,
          mem_univ _, ?_⟩
        simp [privFun, slot]
  exact hempty (hsub hon)

noncomputable def centerIdx (G : Geom) (i : Fin 2) : Fin 111 :=
  if i = 0 then G.p else G.q

lemma centerIdx_spec (G : Geom) (a : Fin 4) (i : Fin 2) :
    (G.A (lineP G a) (centerIdx G i) = true ↔ i = 0) ∧
      (G.A (lineQ G a) (centerIdx G i) = true ↔ i = 1) := by
  fin_cases i
  · simp [centerIdx, lineP_on_p, lineQ_off_p]
  · simp [centerIdx, lineP_off_q, lineQ_on_q]

lemma eq_decide_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) : b = decide P := by
  cases b
  · have hnot : ¬ P := by
      intro hP
      have : (false : Bool) = true := h.mpr hP
      cases this
    rw [decide_eq_false hnot]
  · have hP : P := h.mp rfl
    rw [decide_eq_true hP]

noncomputable def colMap (G : Geom) : Idx723 → Fin 111
  | .inl (.inl (a, b)) => codePoint G a b
  | .inl (.inr (.inl i)) => centerIdx G i
  | .inl (.inr (.inr (b, i))) => privFun G (b, i)
  | .inr t => emptyFun G t

lemma colMap_inj (G : Geom) : Function.Injective (colMap G) := by
  intro x y hxy
  match x, y with
  | .inl (.inl ⟨a, b⟩), .inl (.inl ⟨c, d⟩) =>
      have hxy' : codePoint G a b = codePoint G c d := by simpa [colMap] using hxy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (codePoint_inj G hxy')
      rfl
  | .inl (.inl ⟨a, b⟩), .inl (.inr (.inl i)) =>
      apply False.elim
      have hS := codePoint_mem G a b
      fin_cases i
      · simp [colMap, centerIdx] at hxy
        exact G.hp (hxy ▸ hS)
      · simp [colMap, centerIdx] at hxy
        exact G.hq (hxy ▸ hS)
  | .inl (.inl ⟨a, b⟩), .inl (.inr (.inr ⟨c, j⟩)) =>
      apply False.elim
      exact priv_not_S G c (privFun_mem G (c, j))
        ((by simpa [colMap] using hxy) ▸ codePoint_mem G a b)
  | .inl (.inl ⟨a, b⟩), .inr t =>
      apply False.elim
      have hnot : emptyFun G t ∉ covered G := (mem_sdiff.mp (slot_mem _ _ t)).2
      exact hnot ((by simpa [colMap] using hxy) ▸
        mem_union_left _ (mem_union_left _ (codePoint_mem G a b)))
  | .inl (.inr (.inl i)), .inl (.inl ⟨a, b⟩) =>
      apply False.elim
      have hS := codePoint_mem G a b
      fin_cases i
      · simp [colMap, centerIdx] at hxy
        exact G.hp (hxy.symm ▸ hS)
      · simp [colMap, centerIdx] at hxy
        exact G.hq (hxy.symm ▸ hS)
  | .inl (.inr (.inl i)), .inl (.inr (.inl j)) =>
      fin_cases i <;> fin_cases j
      · rfl
      · simp [colMap, centerIdx] at hxy
        exact (G.hpq hxy).elim
      · simp [colMap, centerIdx] at hxy
        exact (G.hpq hxy.symm).elim
      · rfl
  | .inl (.inr (.inl i)), .inl (.inr (.inr ⟨b, j⟩)) =>
      apply False.elim
      fin_cases i
      · simp [colMap, centerIdx] at hxy
        exact priv_ne_p G (b, j) hxy.symm
      · simp [colMap, centerIdx] at hxy
        exact priv_ne_q G (b, j) hxy.symm
  | .inl (.inr (.inl i)), .inr t =>
      apply False.elim
      have hnot : emptyFun G t ∉ covered G := (mem_sdiff.mp (slot_mem _ _ t)).2
      fin_cases i
      · simp [colMap, centerIdx] at hxy
        exact hnot (hxy ▸ mem_union_left _ (mem_union_right _ (by simp [centers])))
      · simp [colMap, centerIdx] at hxy
        exact hnot (hxy ▸ mem_union_left _ (mem_union_right _ (by simp [centers])))
  | .inl (.inr (.inr ⟨b, i⟩)), .inl (.inl ⟨a, c⟩) =>
      apply False.elim
      exact priv_not_S G b (privFun_mem G (b, i))
        ((by simpa [colMap] using hxy.symm) ▸ codePoint_mem G a c)
  | .inl (.inr (.inr ⟨b, j⟩)), .inl (.inr (.inl i)) =>
      apply False.elim
      fin_cases i
      · simp [colMap, centerIdx] at hxy
        exact priv_ne_p G (b, j) hxy
      · simp [colMap, centerIdx] at hxy
        exact priv_ne_q G (b, j) hxy
  | .inl (.inr (.inr ⟨b, i⟩)), .inl (.inr (.inr ⟨c, j⟩)) =>
      have hxy' : privFun G (b, i) = privFun G (c, j) := by simpa [colMap] using hxy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (privFun_inj G hxy')
      rfl
  | .inl (.inr (.inr ⟨b, i⟩)), .inr t =>
      apply False.elim
      have hmem : privFun G (b, i) ∈ covered G :=
        mem_union_right _ (mem_image.mpr ⟨(b, i), mem_univ _, rfl⟩)
      have hnot : emptyFun G t ∉ covered G := (mem_sdiff.mp (slot_mem _ _ t)).2
      exact hnot ((by simpa [colMap] using hxy) ▸ hmem)
  | .inr t, .inl (.inl ⟨a, b⟩) =>
      apply False.elim
      have hnot : emptyFun G t ∉ covered G := (mem_sdiff.mp (slot_mem _ _ t)).2
      exact hnot ((by simpa [colMap] using hxy.symm) ▸
        mem_union_left _ (mem_union_left _ (codePoint_mem G a b)))
  | .inr t, .inl (.inr (.inl i)) =>
      apply False.elim
      have hnot : emptyFun G t ∉ covered G := (mem_sdiff.mp (slot_mem _ _ t)).2
      fin_cases i
      · simp [colMap, centerIdx] at hxy
        exact hnot (hxy.symm ▸ mem_union_left _ (mem_union_right _ (by simp [centers])))
      · simp [colMap, centerIdx] at hxy
        exact hnot (hxy.symm ▸ mem_union_left _ (mem_union_right _ (by simp [centers])))
  | .inr t, .inl (.inr (.inr ⟨b, i⟩)) =>
      apply False.elim
      have hmem : privFun G (b, i) ∈ covered G :=
        mem_union_right _ (mem_image.mpr ⟨(b, i), mem_univ _, rfl⟩)
      have hnot : emptyFun G t ∉ covered G := (mem_sdiff.mp (slot_mem _ _ t)).2
      exact hnot ((by simpa [colMap] using hxy.symm) ▸ hmem)
  | .inr t, .inr s =>
      obtain rfl := slot_inj (emptyCols G) (empty_card G) (by simpa [colMap, emptyFun] using hxy)
      rfl

lemma card_Idx : Fintype.card Idx723 = 111 := by
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

lemma colMap_bij (G : Geom) : Function.Bijective (colMap G) := by
  refine ⟨colMap_inj G, ?_⟩
  intro y
  let e : Idx723 ≃ Fin 111 :=
    Fintype.equivFinOfCardEq (card_Idx.trans (Fintype.card_fin (n := 111)).symm)
  have hinj : Function.Injective (colMap G ∘ e.symm) := (colMap_inj G).comp e.symm.injective
  obtain ⟨i, hi⟩ := (Function.Injective.bijective_of_finite hinj).2 y
  exact ⟨e.symm i, hi⟩

noncomputable def colEquiv (G : Geom) : Idx723 ≃ Fin 111 :=
  Equiv.ofBijective (colMap G) (colMap_bij G)

lemma canonical (G : Geom) :
    ∃ (r : L723 ≃ Fin 8) (c : Idx723 ≃ Fin 111),
      (∀ x, c x ∈ G.S ↔ ∃ a b : Fin 4, x = .inl (.inl (a, b))) ∧
      (∀ a b j, G.A (r (.inl a)) (c (.inl (.inl (b, j)))) = decide (a = b)) ∧
      (∀ a b j, G.A (r (.inr a)) (c (.inl (.inl (j, b)))) = decide (a = b)) ∧
      (∀ a : Fin 4, ∀ i : Fin 2,
        G.A (r (.inl a)) (c (.inl (.inr (.inl i)))) = decide (i = 0) ∧
        G.A (r (.inr a)) (c (.inl (.inr (.inl i)))) = decide (i = 1)) ∧
      (∀ a b i, G.A (r a) (c (.inl (.inr (.inr (b, i))))) = decide (a = b)) ∧
      ∀ a i, G.A (r a) (c (.inr i)) = false := by
  refine ⟨lineEquiv G, colEquiv G, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hS
      match x with
      | .inl (.inl ⟨a, b⟩) => exact ⟨a, b, rfl⟩
      | .inl (.inr (.inl i)) =>
          fin_cases i <;> simp [colEquiv, colMap, centerIdx, G.hp, G.hq] at hS
      | .inl (.inr (.inr ⟨b, i⟩)) =>
          exact (priv_not_S G b (privFun_mem G (b, i)) (by simpa [colEquiv, colMap] using hS)).elim
      | .inr t =>
          have hnot : emptyFun G t ∉ G.S := by
            intro h
            have hcov : emptyFun G t ∈ covered G :=
              mem_union_left _ (mem_union_left _ h)
            exact (mem_sdiff.mp (slot_mem _ _ t)).2 hcov
          exact (hnot (by simpa [colEquiv, colMap] using hS)).elim
    · intro hex
      obtain ⟨a, b, rfl⟩ := hex
      simpa [colEquiv, colMap] using codePoint_mem G a b
  · intro a b j
    apply eq_decide_of_iff
    simpa [lineEquiv, colEquiv, colMap, lineMap] using
      ((lines_at_code G b j (lineP G a)).trans
        ⟨fun h => by
            rcases h with h1 | h1
            · exact lineP_inj G h1
            · exact (lineP_ne_lineQ G a j h1).elim,
          fun h => Or.inl (congrArg (lineP G) h)⟩)
  · intro a b j
    apply eq_decide_of_iff
    simpa [lineEquiv, colEquiv, colMap, lineMap] using
      ((lines_at_code G j b (lineQ G a)).trans
        ⟨fun h => by
            rcases h with h1 | h1
            · exact (lineP_ne_lineQ G j a h1.symm).elim
            · exact lineQ_inj G h1,
          fun h => Or.inr (congrArg (lineQ G) h)⟩)
  · intro a i
    constructor
    · apply eq_decide_of_iff
      simpa [lineEquiv, colEquiv, colMap, lineMap] using (centerIdx_spec G a i).1
    · apply eq_decide_of_iff
      simpa [lineEquiv, colEquiv, colMap, lineMap] using (centerIdx_spec G a i).2
  · intro a b i
    apply eq_decide_of_iff
    simpa [lineEquiv, colEquiv, colMap] using privFun_only G a b i
  · intro a i
    simpa [lineEquiv, colEquiv, colMap] using empty_off G a i

end

theorem OMA.solution :
    OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1.H1 := by
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1.H1
  dsimp only
  intro A S hcardS hrow hsec hdeg hpair p q hp hq hpq hfourP hfourQ hblock
  exact canonical
    { A := A
      S := S
      p := p
      q := q
      cardS := hcardS
      hrow := hrow
      hsec := hsec
      hdeg := hdeg
      hpair := hpair
      hp := hp
      hq := hq
      hpq := hpq
      hfourP := hfourP
      hfourQ := hfourQ
      hblock := hblock }
