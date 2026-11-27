import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.NormNum

-- Each pair of the eight points meets in one column, each column has at most two points,
-- and each point lies on eleven columns. The columns are then a permutation of the
-- twenty-eight pair columns, thirty-two private columns, and fifty-one empty columns.

abbrev Q723 := {q : Fin 8 × Fin 8 // q.1 < q.2}

def block (A : Fin 8 → Fin 111 → Bool) (p : Fin 111) : Finset (Fin 8) :=
  Finset.univ.filter fun a => A a p = true

def line (A : Fin 8 → Fin 111 → Bool) (a : Fin 8) : Finset (Fin 111) :=
  Finset.univ.filter fun p => A a p = true

@[simp] lemma mem_block {A : Fin 8 → Fin 111 → Bool} {p : Fin 111} {a : Fin 8} :
    a ∈ block A p ↔ A a p = true := by
  simp [block]

@[simp] lemma mem_line {A : Fin 8 → Fin 111 → Bool} {a : Fin 8} {p : Fin 111} :
    p ∈ line A a ↔ A a p = true := by
  simp [line]

structure Geom where
  A : Fin 8 → Fin 111 → Bool
  hpair : ∀ a b : Fin 8, a ≠ b → ∃! p : Fin 111, A a p = true ∧ A b p = true
  hcol : ∀ p : Fin 111, (block A p).card ≤ 2
  hrow : ∀ a : Fin 8, (line A a).card = 11

noncomputable def pairCol (G : Geom) (a b : Fin 8) (hab : a ≠ b) : Fin 111 :=
  Classical.choose (G.hpair a b hab)

lemma pair_left (G : Geom) (a b : Fin 8) (hab : a ≠ b) :
    G.A a (pairCol G a b hab) = true :=
  ((Classical.choose_spec (G.hpair a b hab)).1).1

lemma pair_right (G : Geom) (a b : Fin 8) (hab : a ≠ b) :
    G.A b (pairCol G a b hab) = true :=
  ((Classical.choose_spec (G.hpair a b hab)).1).2

lemma pair_unique_eq (G : Geom) (a b : Fin 8) (hab : a ≠ b) {p : Fin 111}
    (hp : G.A a p = true ∧ G.A b p = true) : p = pairCol G a b hab :=
  (Classical.choose_spec (G.hpair a b hab)).2 p hp

lemma pair_on (G : Geom) (a b : Fin 8) (hab : a ≠ b) :
    block G.A (pairCol G a b hab) = {a, b} := by
  set p := pairCol G a b hab
  have ha : a ∈ block G.A p := by simpa [mem_block] using pair_left G a b hab
  have hb : b ∈ block G.A p := by simpa [mem_block] using pair_right G a b hab
  have hsub : ({a, b} : Finset (Fin 8)) ⊆ block G.A p := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hle : (block G.A p).card ≤ ({a, b} : Finset (Fin 8)).card := by
    rw [Finset.card_pair_eq_two_iff.mpr hab]
    exact G.hcol p
  exact (Finset.eq_of_subset_of_card_le hsub hle).symm

noncomputable def rowPairFun (G : Geom) (a : Fin 8)
    (b : {x : Fin 8 // x ∈ Finset.univ.erase a}) : Fin 111 :=
  pairCol G a b.1 ((Finset.mem_erase.mp b.2).1.symm)

noncomputable def rowPairs (G : Geom) (a : Fin 8) : Finset (Fin 111) :=
  ((Finset.univ.erase a).attach).image (rowPairFun G a)

lemma rowPairFun_inj (G : Geom) (a : Fin 8) : Function.Injective (rowPairFun G a) := by
  intro b c h
  have hb : block G.A (rowPairFun G a b) = {a, b.1} := by
    simpa [rowPairFun] using pair_on G a b.1 ((Finset.mem_erase.mp b.2).1.symm)
  have hc : block G.A (rowPairFun G a c) = {a, c.1} := by
    simpa [rowPairFun] using pair_on G a c.1 ((Finset.mem_erase.mp c.2).1.symm)
  have hset : ({a, b.1} : Finset (Fin 8)) = {a, c.1} := by
    rw [← hb, ← hc]
    exact congrArg (block G.A) h
  have hmem : b.1 ∈ ({a, c.1} : Finset (Fin 8)) := by
    rw [← hset]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hba | hbc
  · exact absurd hba (Finset.mem_erase.mp b.2).1
  · exact Subtype.ext hbc

lemma rowPairs_card (G : Geom) (a : Fin 8) : (rowPairs G a).card = 7 := by
  rw [rowPairs, Finset.card_image_of_injective _ (rowPairFun_inj G a), Finset.card_attach,
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]

lemma rowPairs_subset (G : Geom) (a : Fin 8) : rowPairs G a ⊆ line G.A a := by
  intro p hp
  rw [rowPairs, Finset.mem_image] at hp
  obtain ⟨b, _, rfl⟩ := hp
  rw [mem_line, rowPairFun]
  exact pair_left G a b.1 ((Finset.mem_erase.mp b.2).1.symm)

lemma pairCol_mem_rowPairs (G : Geom) {a b : Fin 8} (hab : a ≠ b) :
    pairCol G a b hab ∈ rowPairs G a := by
  let c : {x : Fin 8 // x ∈ Finset.univ.erase a} := ⟨b, Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩⟩
  have h' : a ≠ b := (Finset.mem_erase.mp c.2).1.symm
  have hsame : pairCol G a b h' = pairCol G a b hab :=
    pair_unique_eq G a b hab ⟨pair_left G a b h', pair_right G a b h'⟩
  have hrfl : rowPairFun G a c = pairCol G a b h' := rfl
  exact Finset.mem_image.mpr ⟨c, Finset.mem_attach _ c, hrfl.trans hsame⟩

noncomputable def privSet (G : Geom) (a : Fin 8) : Finset (Fin 111) :=
  line G.A a \ rowPairs G a

lemma priv_card (G : Geom) (a : Fin 8) : (privSet G a).card = 4 := by
  rw [privSet, Finset.card_sdiff_of_subset (rowPairs_subset G a), G.hrow a, rowPairs_card G a]

lemma priv_on (G : Geom) {a : Fin 8} {p : Fin 111} (hp : p ∈ privSet G a) :
    block G.A p = {a} := by
  have hmem : p ∈ line G.A a := (Finset.mem_sdiff.mp hp).1
  have hnot : p ∉ rowPairs G a := (Finset.mem_sdiff.mp hp).2
  have ha : a ∈ block G.A p := by
    rw [mem_block]
    rwa [mem_line] at hmem
  have hne2 : (block G.A p).card ≠ 2 := by
    intro h2
    obtain ⟨x, y, hxy, heq⟩ := Finset.card_eq_two.mp h2
    have ha' : a = x ∨ a = y := by
      have : a ∈ block G.A p := ha
      rw [heq] at this
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    rcases ha' with rfl | rfl
    · have hy : G.A y p = true := by
        have : y ∈ block G.A p := by rw [heq]; simp
        rwa [mem_block] at this
      have hp' : p = pairCol G a y hxy := pair_unique_eq G a y hxy ⟨by rwa [mem_block] at ha, hy⟩
      exact hnot (hp'.symm ▸ pairCol_mem_rowPairs G hxy)
    · have hx : G.A x p = true := by
        have : x ∈ block G.A p := by rw [heq]; simp
        rwa [mem_block] at this
      have hxa : a ≠ x := hxy.symm
      have hp' : p = pairCol G a x hxa := pair_unique_eq G a x hxa ⟨by rwa [mem_block] at ha, hx⟩
      exact hnot (hp'.symm ▸ pairCol_mem_rowPairs G hxa)
  have hge : 1 ≤ (block G.A p).card := by
    rw [← Finset.card_singleton a]
    exact Finset.card_le_card (Finset.singleton_subset_iff.mpr ha)
  have hle := G.hcol p
  have hcard : (block G.A p).card = 1 := by omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
  have hb' : a = b := by
    have : a ∈ ({b} : Finset (Fin 8)) := by rw [← hb]; exact ha
    simpa using this
  rw [hb, hb']

lemma singleton_mem_priv (G : Geom) {a : Fin 8} {p : Fin 111} (hs : block G.A p = {a}) :
    p ∈ privSet G a := by
  have ha : G.A a p = true := by
    have : a ∈ block G.A p := by rw [hs]; simp
    rwa [mem_block] at this
  rw [privSet, Finset.mem_sdiff]
  refine ⟨by rwa [mem_line], ?_⟩
  intro hin
  rw [rowPairs, Finset.mem_image] at hin
  obtain ⟨b, _, hbq⟩ := hin
  have hon := pair_on G a b.1 ((Finset.mem_erase.mp b.2).1.symm)
  have hrfl : rowPairFun G a b = pairCol G a b.1 ((Finset.mem_erase.mp b.2).1.symm) := rfl
  rw [hrfl] at hbq
  rw [hbq] at hon
  rw [hs] at hon
  have hbmem : b.1 ∈ ({a, b.1} : Finset (Fin 8)) := by simp
  rw [← hon] at hbmem
  simp only [Finset.mem_singleton] at hbmem
  exact (Finset.mem_erase.mp b.2).1 hbmem

lemma priv_disjoint (G : Geom) {a b : Fin 8} (hab : a ≠ b) :
    Disjoint (privSet G a) (privSet G b) := by
  rw [Finset.disjoint_left]
  intro p hpa hpb
  have hon := priv_on G hpa
  have hother := priv_on G hpb
  have : ({a} : Finset (Fin 8)) = {b} := by rw [← hon, hother]
  have : a = b := by simpa using this
  exact hab this

noncomputable def slotEquiv {n : ℕ} (s : Finset (Fin 111)) (hs : s.card = n) : s ≃ Fin n :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hs])

noncomputable def slot {n : ℕ} (s : Finset (Fin 111)) (hs : s.card = n) (i : Fin n) : Fin 111 :=
  ((slotEquiv s hs).symm i).1

lemma slot_mem {n : ℕ} (s : Finset (Fin 111)) (hs : s.card = n) (i : Fin n) : slot s hs i ∈ s :=
  ((slotEquiv s hs).symm i).2

lemma slot_inj {n : ℕ} (s : Finset (Fin 111)) (hs : s.card = n) : Function.Injective (slot s hs) := by
  intro i j hij
  apply (slotEquiv s hs).symm.injective
  exact Subtype.ext hij

lemma slot_surj {n : ℕ} (s : Finset (Fin 111)) (hs : s.card = n) {p : Fin 111} (hp : p ∈ s) :
    ∃ i : Fin n, slot s hs i = p := by
  refine ⟨slotEquiv s hs ⟨p, hp⟩, ?_⟩
  simp only [slot]
  rw [Equiv.symm_apply_apply]

noncomputable def privFun (G : Geom) : Fin 8 × Fin 4 → Fin 111 :=
  fun ⟨a, i⟩ => slot (privSet G a) (priv_card G a) i

lemma privFun_inj (G : Geom) : Function.Injective (privFun G) := by
  intro p q h
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  by_cases hab : a = b
  · subst hab
    exact Prod.ext rfl (slot_inj (privSet G a) (priv_card G a) (by simpa [privFun] using h))
  · have hma := slot_mem (privSet G a) (priv_card G a) i
    have hmb := slot_mem (privSet G b) (priv_card G b) j
    have hcol : slot (privSet G a) (priv_card G a) i = slot (privSet G b) (priv_card G b) j := by
      simpa [privFun] using h
    rw [← hcol] at hmb
    exact (Finset.disjoint_left.mp (priv_disjoint G hab) hma hmb).elim

noncomputable def privImage (G : Geom) : Finset (Fin 111) :=
  Finset.univ.image (privFun G)

lemma privImage_card (G : Geom) : (privImage G).card = 32 := by
  rw [privImage, Finset.card_image_of_injective _ (privFun_inj G), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

lemma ordered_pair_eq {a b c d : Fin 8} (hab : a < b) (hcd : c < d)
    (h : ({a, b} : Finset (Fin 8)) = {c, d}) : a = c ∧ b = d := by
  have ha : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Finset (Fin 8)) := by rw [← h]; simp
    simpa [Finset.mem_insert, Finset.mem_singleton] using this
  have hb : b = c ∨ b = d := by
    have : b ∈ ({c, d} : Finset (Fin 8)) := by rw [← h]; simp
    simpa [Finset.mem_insert, Finset.mem_singleton] using this
  rcases ha with h1 | h1
  · rcases hb with h2 | h2
    · exact absurd (h1.trans h2.symm) (ne_of_lt hab)
    · exact ⟨h1, h2⟩
  · rcases hb with h2 | h2
    · have hba : b < a := by simpa [h1, h2] using hcd
      exact absurd hba (lt_asymm hab)
    · exact absurd (h1.trans h2.symm) (ne_of_lt hab)

noncomputable def pairFun (G : Geom) (q : Q723) : Fin 111 :=
  pairCol G q.1.1 q.1.2 (ne_of_lt q.2)

lemma pairFun_on (G : Geom) (q : Q723) : block G.A (pairFun G q) = {q.1.1, q.1.2} := by
  simpa [pairFun] using pair_on G q.1.1 q.1.2 (ne_of_lt q.2)

lemma pairFun_inj (G : Geom) : Function.Injective (pairFun G) := by
  intro q r h
  have hset : ({q.1.1, q.1.2} : Finset (Fin 8)) = {r.1.1, r.1.2} := by
    rw [← pairFun_on G q, ← pairFun_on G r]
    exact congrArg (block G.A) h
  have key := ordered_pair_eq q.2 r.2 hset
  apply Subtype.ext
  exact Prod.ext key.1 key.2

set_option maxHeartbeats 2000000 in
lemma card_Q723 : Fintype.card Q723 = 28 := by
  classical
  rw [Fintype.card_subtype]
  decide

noncomputable def pairImage (G : Geom) : Finset (Fin 111) :=
  (Finset.univ : Finset Q723).image (pairFun G)

lemma pairImage_card (G : Geom) : (pairImage G).card = 28 := by
  rw [pairImage, Finset.card_image_of_injective _ (pairFun_inj G), Finset.card_univ, card_Q723]

lemma support_card_pairFun (G : Geom) (q : Q723) : (block G.A (pairFun G q)).card = 2 := by
  rw [pairFun_on G q, Finset.card_pair_eq_two_iff.mpr (ne_of_lt q.2)]

lemma support_card_privFun (G : Geom) (t : Fin 8 × Fin 4) : (block G.A (privFun G t)).card = 1 := by
  rcases t with ⟨a, i⟩
  have hmem := slot_mem (privSet G a) (priv_card G a) i
  simp [privFun, priv_on G hmem, Finset.card_singleton]

lemma pair_mem_image (G : Geom) {p : Fin 111} (h2 : (block G.A p).card = 2) : p ∈ pairImage G := by
  obtain ⟨x, y, hxy, heq⟩ := Finset.card_eq_two.mp h2
  have hx : G.A x p = true := by
    have : x ∈ block G.A p := by rw [heq]; simp
    rwa [mem_block] at this
  have hy : G.A y p = true := by
    have : y ∈ block G.A p := by rw [heq]; simp
    rwa [mem_block] at this
  rcases lt_trichotomy x y with hlt | heqxy | hgt
  · let q : Q723 := ⟨(x, y), hlt⟩
    have : pairFun G q = p := by
      simpa [pairFun, q] using (pair_unique_eq G x y (ne_of_lt hlt) ⟨hx, hy⟩).symm
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, this⟩
  · exact absurd heqxy hxy
  · let q : Q723 := ⟨(y, x), hgt⟩
    have : pairFun G q = p := by
      simpa [pairFun, q] using (pair_unique_eq G y x (ne_of_lt hgt) ⟨hy, hx⟩).symm
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, this⟩

lemma card_one_mem_privImage (G : Geom) {p : Fin 111} (h1 : (block G.A p).card = 1) :
    p ∈ privImage G := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hpriv : p ∈ privSet G a := singleton_mem_priv G (by rw [ha])
  obtain ⟨i, hi⟩ := slot_surj (privSet G a) (priv_card G a) hpriv
  refine Finset.mem_image.mpr ⟨(⟨a, i⟩ : Fin 8 × Fin 4), Finset.mem_univ _, ?_⟩
  simpa [privFun] using hi

lemma pair_priv_images_disjoint (G : Geom) : Disjoint (pairImage G) (privImage G) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp hpriv
  rw [pairImage, Finset.mem_image] at hp
  rw [privImage, Finset.mem_image] at hpriv
  rcases hp with ⟨q, -, hqeq⟩
  rcases hpriv with ⟨t, -, hteq⟩
  have h2 := support_card_pairFun G q
  have h1 := support_card_privFun G t
  rw [hqeq] at h2
  rw [hteq] at h1
  omega

noncomputable def covered (G : Geom) : Finset (Fin 111) :=
  pairImage G ∪ privImage G

lemma covered_card (G : Geom) : (covered G).card = 60 := by
  rw [covered, Finset.card_union_of_disjoint (pair_priv_images_disjoint G), pairImage_card G,
    privImage_card G]

noncomputable def emptyCols (G : Geom) : Finset (Fin 111) :=
  Finset.univ \ covered G

lemma empty_card (G : Geom) : (emptyCols G).card = 51 := by
  rw [emptyCols, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, covered_card G]

lemma block_empty (G : Geom) {p : Fin 111} (hp : p ∈ emptyCols G) : block G.A p = ∅ := by
  have hnot : p ∉ covered G := (Finset.mem_sdiff.mp hp).2
  have hne2 : (block G.A p).card ≠ 2 := by
    intro h2
    exact hnot (Finset.mem_union_left _ (pair_mem_image G h2))
  have hne1 : (block G.A p).card ≠ 1 := by
    intro h1
    exact hnot (Finset.mem_union_right _ (card_one_mem_privImage G h1))
  have hle := G.hcol p
  have h0 : (block G.A p).card = 0 := by omega
  exact Finset.card_eq_zero.mp h0

noncomputable def emptyFun (G : Geom) (t : Fin 51) : Fin 111 :=
  slot (emptyCols G) (empty_card G) t

lemma support_card_emptyFun (G : Geom) (t : Fin 51) : (block G.A (emptyFun G t)).card = 0 := by
  unfold emptyFun
  rw [block_empty G (slot_mem (emptyCols G) (empty_card G) t), Finset.card_empty]

lemma pair_ne_priv (G : Geom) (q : Q723) (t : Fin 8 × Fin 4) : pairFun G q ≠ privFun G t := by
  intro h
  have h2 := support_card_pairFun G q
  rw [h] at h2
  rw [support_card_privFun G t] at h2
  omega

lemma pair_ne_empty (G : Geom) (q : Q723) (t : Fin 51) : pairFun G q ≠ emptyFun G t := by
  intro h
  have h2 := support_card_pairFun G q
  rw [h] at h2
  rw [support_card_emptyFun G t] at h2
  omega

lemma priv_ne_empty (G : Geom) (t : Fin 8 × Fin 4) (u : Fin 51) : privFun G t ≠ emptyFun G u := by
  intro h
  have h1 := support_card_privFun G t
  rw [h] at h1
  rw [support_card_emptyFun G u] at h1
  omega

def glue {α β γ δ : Type} (f : α → δ) (g : β → δ) (k : γ → δ) : (α ⊕ β) ⊕ γ → δ
  | .inl (.inl a) => f a
  | .inl (.inr b) => g b
  | .inr c => k c

lemma glue_inj {α β γ δ : Type} {f : α → δ} {g : β → δ} {k : γ → δ}
    (hf : Function.Injective f) (hg : Function.Injective g) (hk : Function.Injective k)
    (hfg : ∀ a b, f a ≠ g b) (hfk : ∀ a c, f a ≠ k c) (hgk : ∀ b c, g b ≠ k c) :
    Function.Injective (glue f g k) := by
  intro x y hxy
  match x, y with
  | .inl (.inl a), .inl (.inl a') =>
      obtain rfl := hf (by simpa [glue] using hxy)
      rfl
  | .inl (.inl a), .inl (.inr b) =>
      exact (hfg a b (by simpa [glue] using hxy)).elim
  | .inl (.inl a), .inr c =>
      exact (hfk a c (by simpa [glue] using hxy)).elim
  | .inl (.inr b), .inl (.inl a) =>
      exact (hfg a b (by simpa [glue] using hxy.symm)).elim
  | .inl (.inr b), .inl (.inr b') =>
      obtain rfl := hg (by simpa [glue] using hxy)
      rfl
  | .inl (.inr b), .inr c =>
      exact (hgk b c (by simpa [glue] using hxy)).elim
  | .inr c, .inl (.inl a) =>
      exact (hfk a c (by simpa [glue] using hxy.symm)).elim
  | .inr c, .inl (.inr b) =>
      exact (hgk b c (by simpa [glue] using hxy.symm)).elim
  | .inr c, .inr c' =>
      obtain rfl := hk (by simpa [glue] using hxy)
      rfl

noncomputable def colMap (G : Geom) :
    ((Q723 ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51) → Fin 111 :=
  glue (pairFun G) (privFun G) (emptyFun G)

lemma emptyFun_inj (G : Geom) : Function.Injective (emptyFun G) := by
  intro a b h
  apply slot_inj (emptyCols G) (empty_card G)
  simpa [emptyFun] using h

lemma colMap_inj (G : Geom) : Function.Injective (colMap G) := by
  unfold colMap
  exact glue_inj (pairFun_inj G) (privFun_inj G) (emptyFun_inj G)
    (pair_ne_priv G) (pair_ne_empty G) (priv_ne_empty G)

lemma card_index : Fintype.card ((Q723 ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51) = 111 := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, card_Q723]

lemma colMap_bij (G : Geom) : Function.Bijective (colMap G) := by
  let e : ((Q723 ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51) ≃ Fin 111 := Fintype.equivFinOfCardEq card_index
  have hinj : Function.Injective (colMap G ∘ e.symm) := (colMap_inj G).comp e.symm.injective
  have hbij : Function.Bijective (colMap G ∘ e.symm) := hinj.bijective_of_finite
  have hcomp : colMap G = (colMap G ∘ e.symm) ∘ e := by
    ext x
    simp
  rw [hcomp]
  exact hbij.comp e.bijective

lemma eq_decide_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) : b = decide P := by
  cases b
  · have hnot : ¬ P := by
      intro hP
      have : (false : Bool) = true := h.mpr hP
      cases this
    rw [decide_eq_false hnot]
  · have hP : P := h.mp rfl
    rw [decide_eq_true hP]

theorem OMA.solution :
    OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro A hpair hcol hrow
  let G : Geom := ⟨A, hpair, hcol, hrow⟩
  let f := colMap G
  have hf := colMap_bij G
  let e := Equiv.ofBijective f hf
  refine ⟨e, ?_, ?_, ?_⟩
  · intro r q
    change A r (f (.inl (.inl q))) = _
    have hcolv : f (.inl (.inl q)) = pairFun G q := by simp [f, colMap, glue]
    rw [hcolv]
    apply eq_decide_of_iff
    rw [← mem_block, pairFun_on G q]
    simp [Finset.mem_insert, Finset.mem_singleton]
  · intro r s i
    change A r (f (.inl (.inr (s, i)))) = _
    have hcolv : f (.inl (.inr (s, i))) = privFun G (s, i) := by simp [f, colMap, glue]
    rw [hcolv]
    apply eq_decide_of_iff
    have hmem := slot_mem (privSet G s) (priv_card G s) i
    rw [← mem_block, privFun, priv_on G hmem]
    simp
  · intro r t
    change A r (f (.inr t)) = false
    have hcolv : f (.inr t) = emptyFun G t := by simp [f, colMap, glue]
    rw [hcolv]
    have hempty : block A (emptyFun G t) = ∅ := by
      unfold emptyFun
      simpa [G] using block_empty G (slot_mem (emptyCols G) (empty_card G) t)
    cases hA : A r (emptyFun G t)
    · rfl
    · have hr : r ∈ block A (emptyFun G t) := by simpa [mem_block] using hA
      rw [hempty] at hr
      simp at hr
