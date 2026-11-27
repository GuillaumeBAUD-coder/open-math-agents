import FormalConjectures.ErdosProblems.«629»

/-!
# The Hanson–MacGillivray–Toft recursion

Pad each list of a minimum obstruction for k-2 colors with one fresh pair.
Auxiliary vertices carry transversals of the k fresh pairs. Parity assigns
them to the two sides and forces a missed list whenever each pair contains
a color from a given side. The number of auxiliary vertices is 2^k.

Reference: Hanson, MacGillivray and Toft, Choosability of Bipartite Graphs,
Theorem 3. The same argument at k=2 uses the obstruction to 0-choosability.
-/

/- Finite obstructions to bipartite list coloring. -/

open SimpleGraph

-- The following three lemmas are from Ian Qvist’s proof in pull request 80.
lemma OMA.property_b_choosable_mono {V : Type*} {G : SimpleGraph V} {k l : ℕ}
    (hkl : k ≤ l) (hk : G.IsKChoosable k) : G.IsKChoosable l := by
  intro L hL
  have hex (v : V) : ∃ M ⊆ L v, (M : Finset ℕ).card = k :=
    Finset.exists_subset_card_eq (by rw [hL]; exact hkl)
  choose M hM_sub hM_card using hex
  obtain ⟨C, hC⟩ := hk M hM_card
  exact ⟨C, fun v => hM_sub v (hC v)⟩

lemma OMA.property_b_finite_choosable {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.IsKChoosable (Fintype.card V) := by
  intro L hL
  have hHall (S : Finset V) : S.card ≤ (S.biUnion L).card := by
    by_cases hS : S.Nonempty
    · obtain ⟨v, hv⟩ := hS
      calc
        S.card ≤ Fintype.card V := Finset.card_le_univ S
        _ = (L v).card := (hL v).symm
        _ ≤ (S.biUnion L).card := Finset.card_le_card fun c hc =>
          Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
    · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hEmpty]
  obtain ⟨c, hc_inj, hc_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hHall
  exact ⟨Coloring.mk c (fun h => hc_inj.ne h.ne), hc_mem⟩

lemma OMA.property_b_to_bipartite {k m : ℕ} (H : Finset (Finset (Fin m)))
    (hU : H.IsUniform k) (hNot : ¬ H.HypergraphColorable 2) :
    ∃ G : SimpleGraph (Fin (2 * H.card)), G.Colorable 2 ∧ k < G.listChromaticNumber := by
  classical
  let e : Fin (2 * H.card) ≃ Fin 2 × ↥H :=
    Fintype.equivOfCardEq (by simp [Fintype.card_prod])
  let G : SimpleGraph (Fin (2 * H.card)) :=
    { Adj := fun a b => (e a).1 ≠ (e b).1
      symm := ⟨fun _ _ h => Ne.symm h⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  let L (v : Fin (2 * H.card)) : Finset ℕ := (e v).2.val.map Fin.valEmbedding
  have hL (v : Fin (2 * H.card)) : (L v).card = k := by
    rw [show L v = (e v).2.val.map Fin.valEmbedding from rfl, Finset.card_map]
    exact hU _ (e v).2.property
  have hBad : ¬ G.IsKChoosable k := by
    intro h
    obtain ⟨C, hC⟩ := h L hL
    let color (x : Fin m) : Fin 2 :=
      if ∃ ed : ↥H, C (e.symm (0, ed)) = x.val then 0 else 1
    apply hNot
    refine ⟨color, ?_⟩
    intro edge he
    let E : ↥H := ⟨edge, he⟩
    have hleft : C (e.symm (0, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (0, E))
    have hright : C (e.symm (1, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (1, E))
    obtain ⟨x, hx, hx_eq⟩ := Finset.mem_map.mp hleft
    obtain ⟨y, hy, hy_eq⟩ := Finset.mem_map.mp hright
    have h0 : color x = 0 := if_pos ⟨E, hx_eq.symm⟩
    have h1 : color y = 1 := by
      apply if_neg
      rintro ⟨F, hF⟩
      have hAdj : G.Adj (e.symm (0, F)) (e.symm (1, E)) := by
        change (e (e.symm (0, F))).1 ≠ (e (e.symm (1, E))).1
        simp
      exact C.valid hAdj (hF.trans hy_eq)
    exact ⟨x, hx, y, hy, by rw [h0, h1]; decide⟩
  have hs : {j : ℕ | G.IsKChoosable j}.Nonempty :=
    ⟨Fintype.card (Fin (2 * H.card)), OMA.property_b_finite_choosable G⟩
  have hmin : G.IsKChoosable G.listChromaticNumber := Nat.sInf_mem hs
  refine ⟨G, ⟨Coloring.mk (fun v => (e v).1) (fun h => h)⟩, ?_⟩
  by_contra! hle
  exact hBad (OMA.property_b_choosable_mono hle hmin)

lemma OMA.hmt_exists_bad_graph (q : ℕ) :
    ∃ m, ∃ G : SimpleGraph (Fin m), G.Colorable 2 ∧ q < G.listChromaticNumber := by
  classical
  let m := 2 * q - 1
  let H := (Finset.univ : Finset (Fin m)).powersetCard q
  have hU : H.IsUniform q := fun e he => (Finset.mem_powersetCard.mp he).2
  have hNot : ¬ H.HypergraphColorable 2 := by
    rintro ⟨c, hc⟩
    let A : Finset (Fin m) := Finset.univ.filter fun x => c x = 0
    let B : Finset (Fin m) := Finset.univ \ A
    have hB : B.card = m - A.card := by
      dsimp [B]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hmono (b : Fin 2) (S : Finset (Fin m)) (hs : q ≤ S.card)
        (hcol : ∀ x ∈ S, c x = b) : False := by
      obtain ⟨e, heS, heCard⟩ := Finset.exists_subset_card_eq hs
      have he : e ∈ H := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heCard⟩
      obtain ⟨x, hx, y, hy, hne⟩ := hc e he
      exact hne ((hcol x (heS hx)).trans (hcol y (heS hy)).symm)
    by_cases hA : q ≤ A.card
    · exact hmono 0 A hA (fun x hx => (Finset.mem_filter.mp hx).2)
    · have hBcard : q ≤ B.card := by dsimp [m] at hB; omega
      apply hmono 1 B hBcard
      intro x hx
      have hxA := (Finset.mem_sdiff.mp hx).2
      have hx0 : c x ≠ 0 := fun h => hxA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hcases : ∀ t : Fin 2, t ≠ 0 → t = 1 := by decide
      exact hcases _ hx0
  exact ⟨_, OMA.property_b_to_bipartite H hU hNot⟩

lemma hmt_old_obstruction (q : ℕ) :
    ∃ (side : Fin (Erdos629.n q) → Bool) (L : Fin (Erdos629.n q) → Finset ℕ),
      (∀ v, (L v).card = q) ∧ (∀ f : ℕ → Bool, ∃ v, ∀ c ∈ L v, f c ≠ side v) := by
  classical
  have hs : {m : ℕ | ∃ G : SimpleGraph (Fin m),
      G.Colorable 2 ∧ q < G.listChromaticNumber}.Nonempty := OMA.hmt_exists_bad_graph q
  obtain ⟨G, ⟨D⟩, hChrom⟩ : ∃ G : SimpleGraph (Fin (Erdos629.n q)),
      G.Colorable 2 ∧ q < G.listChromaticNumber := Nat.sInf_mem hs
  have hBad : ¬ G.IsKChoosable q := fun h => (not_le_of_gt hChrom) (Nat.sInf_le h)
  obtain ⟨L, hL, hNo⟩ : ∃ L : Fin (Erdos629.n q) → Finset ℕ,
      (∀ v, (L v).card = q) ∧ ¬ ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v := by
    by_contra h
    apply hBad
    intro L hL
    by_contra hC
    exact h ⟨L, hL, hC⟩
  let side (v : Fin (Erdos629.n q)) : Bool := decide (D v = 0)
  refine ⟨side, L, hL, ?_⟩
  intro f
  by_contra! hall
  choose color hMem hSide using hall
  have hInj : Function.Injective (fun d : Fin 2 => decide (d = 0)) := by decide
  apply hNo
  refine ⟨Coloring.mk color ?_, hMem⟩
  intro v w hAdj hEq
  apply D.valid hAdj
  exact hInj ((hSide v).symm.trans ((congrArg f hEq).trans (hSide w)))

namespace OMA

/-- A Boolean-side list obstruction witnesses an upper bound for `Erdos629.n`. -/
lemma hmt_n_le_of_obstruction {V : Type} [Fintype V] (k : ℕ) (side : V → Bool)
    (L : V → Finset ℕ) (hsize : ∀ v, (L v).card = k)
    (hbad : ∀ f : ℕ → Bool, ∃ v, ∀ c ∈ L v, f c ≠ side v) :
    Erdos629.n k ≤ Fintype.card V := by
  classical
  let e := (Fintype.equivFin V).symm
  let G : SimpleGraph (Fin (Fintype.card V)) :=
    { Adj := fun x y ↦ side (e x) ≠ side (e y)
      symm := ⟨fun _ _ h ↦ Ne.symm h⟩
      loopless := ⟨fun _ h ↦ h rfl⟩ }
  have hbip : G.Colorable 2 :=
    ⟨SimpleGraph.Coloring.mk (fun x ↦ finTwoEquiv.symm (side (e x)))
      (fun hadj heq ↦ hadj (finTwoEquiv.symm.injective heq))⟩
  have hnot : ¬ G.IsKChoosable k := by
    intro h
    obtain ⟨C, hC⟩ := h (fun x ↦ L (e x)) (fun x ↦ hsize (e x))
    let f (c : ℕ) : Bool :=
      if ∃ x, side (e x) = true ∧ C x = c then true else false
    obtain ⟨v, hv⟩ := hbad f
    let x := e.symm v
    have hx : e x = v := e.apply_symm_apply v
    have hl : C x ∈ L v := hx ▸ hC x
    apply hv (C x) hl
    cases hs : side v
    · apply if_neg
      rintro ⟨y, hy, heq⟩
      have hed : G.Adj y x := by
        change side (e y) ≠ side (e x)
        simp [hy, hx, hs]
      exact C.valid hed heq
    · exact if_pos ⟨x, hx.symm ▸ hs, rfl⟩
  have hex : {j : ℕ | G.IsKChoosable j}.Nonempty :=
    ⟨_, property_b_finite_choosable G⟩
  have hmin : G.IsKChoosable G.listChromaticNumber := Nat.sInf_mem hex
  apply Erdos629.n_le G hbip
  by_contra! hle
  exact hnot (property_b_choosable_mono hle hmin)

end OMA

namespace OMA.ER629HMT

open scoped BigOperators

/-- The XOR of the choices of the second endpoint. -/
def hmt_wordSide {k : ℕ} (f : Fin k → Bool) : Bool :=
  ∑ i, f i

/-- Each bit vector indexes one list. On the false side use the complementary transversal. -/
def hmt_wordPick {k : ℕ} (f : Fin k → Bool) (i : Fin k) : Bool :=
  if hmt_wordSide f then f i else !(f i)

private theorem parity_flip {k : ℕ} (f : Fin k → Bool) (j : Fin k) :
    hmt_wordSide (Function.update f j (!(f j))) = !(hmt_wordSide f) := by
  unfold hmt_wordSide
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ f (Finset.mem_univ j)]
  have hsum : ∑ i ∈ Finset.univ.erase j, Function.update f j (!(f j)) i =
      ∑ i ∈ Finset.univ.erase j, f i :=
    Finset.sum_congr rfl fun i hi ↦ Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  rw [hsum, Function.update_self]
  generalize (∑ i ∈ Finset.univ.erase j, f i) = a
  cases a <;> cases f j <;> decide

private theorem exists_with_parity {k : ℕ} (P : Fin k → Bool → Prop)
    (hP : ∀ i, ∃ b, P i b) (j : Fin k) (hj : ∀ b, P j b) (b : Bool) :
    ∃ f : Fin k → Bool, hmt_wordSide f = b ∧ ∀ i, P i (f i) := by
  choose f hf using hP
  by_cases hp : hmt_wordSide f = b
  · exact ⟨f, hp, hf⟩
  · refine ⟨Function.update f j (!(f j)), ?_, ?_⟩
    · rw [parity_flip]
      cases b <;> cases h : hmt_wordSide f <;> simp_all
    · intro i
      by_cases hi : i = j
      · subst i
        rw [Function.update_self]
        exact hj _
      · rw [Function.update_of_ne hi]
        exact hf i

private theorem exists_bit_of_no_opposite {k : ℕ} (χ : Fin k → Bool → Bool) (b : Bool)
    (h : ¬ ∃ i, ∀ x, χ i x = !b) (i : Fin k) : ∃ x, χ i x = b := by
  by_contra! hn
  apply h
  refine ⟨i, fun x ↦ ?_⟩
  specialize hn x
  cases b <;> cases hχ : χ i x <;> simp_all

private theorem exists_pick_of_monochromatic_pair {k : ℕ} (χ : Fin k → Bool → Bool) (b : Bool)
    (h : ¬ ∃ i, ∀ x, χ i x = !b) (j : Fin k) (hj : ∀ x, χ j x = b) :
    ∃ f : Fin k → Bool, ∀ i, χ i (hmt_wordPick f i) = !(hmt_wordSide f) := by
  let P (i : Fin k) (x : Bool) := χ i (if !b then x else !x) = b
  have hP (i : Fin k) : ∃ x, P i x := by
    obtain ⟨x, hx⟩ := exists_bit_of_no_opposite χ b h i
    cases b
    · exact ⟨x, hx⟩
    · exact ⟨!x, by simpa [P] using hx⟩
  obtain ⟨f, hf, hp⟩ := exists_with_parity P hP j (fun _ ↦ hj _) (!b)
  refine ⟨f, fun i ↦ ?_⟩
  simpa [hmt_wordPick, hf, P] using hp i

/-- Unless both colors occur on monochromatic pairs, a transversal list misses its own side. -/
private theorem exists_pick_of_no_opposite_pairs {k : ℕ} (χ : Fin k → Bool → Bool)
    (h : ¬ ((∃ i, ∀ x, χ i x = false) ∧ (∃ j, ∀ x, χ j x = true))) :
    ∃ f : Fin k → Bool, ∀ i, χ i (hmt_wordPick f i) = !(hmt_wordSide f) := by
  by_cases h0 : ∃ i, ∀ x, χ i x = false
  · obtain ⟨i, hi⟩ := h0
    exact exists_pick_of_monochromatic_pair χ false (fun h1 ↦ h ⟨⟨i, hi⟩, h1⟩) i hi
  by_cases h1 : ∃ i, ∀ x, χ i x = true
  · obtain ⟨i, hi⟩ := h1
    exact exists_pick_of_monochromatic_pair χ true h0 i hi
  choose f hf using exists_bit_of_no_opposite χ false h1
  refine ⟨f, fun i ↦ ?_⟩
  have hagree : χ i (!(f i)) = true := by
    by_contra! hne
    apply h0
    refine ⟨i, fun x ↦ ?_⟩
    have hχ : χ i (!(f i)) = false := Bool.eq_false_iff.mpr hne
    have hd : x = f i ∨ x = !(f i) := by cases x <;> cases f i <;> decide
    rcases hd with hsame | hdiff
    · rw [hsame, hf]
    · rw [hdiff, hχ]
  cases hside : hmt_wordSide f <;> simp [hmt_wordPick, hside, hf i, hagree]

/-- If every pair has an endpoint of one fixed color, a transversal list misses its side. -/
theorem hmt_exists_word {k : ℕ} (color : Fin k → Bool → Bool) (b : Bool)
    (hcolor : ∀ j, ∃ bit, color j bit = b) :
    ∃ w : Fin k → Bool, ∀ j, color j (hmt_wordPick w j) ≠ hmt_wordSide w := by
  have h : ¬ ((∃ i, ∀ x, color i x = false) ∧ (∃ j, ∀ x, color j x = true)) := by
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    cases b
    · obtain ⟨x, hx⟩ := hcolor j
      simp [hj x] at hx
    · obtain ⟨x, hx⟩ := hcolor i
      simp [hi x] at hx
  obtain ⟨w, hw⟩ := exists_pick_of_no_opposite_pairs color h
  refine ⟨w, fun j ↦ ?_⟩
  rw [hw j]
  cases hmt_wordSide w <;> decide

end OMA.ER629HMT

/- Encode the fresh pairs and the old color lists in a disjoint palette. -/

namespace OMA

private def hmt_color {k : ℕ} (j : Fin k) (b : Bool) : ℕ :=
  2 * j.val + b.toNat

private def hmt_paddedList {k : ℕ} (j : Fin k) (L : Finset ℕ) : Finset ℕ :=
  insert (hmt_color j false) (insert (hmt_color j true) (L.image fun c => c + 2 * k))

private lemma hmt_paddedList_card {k : ℕ} (j : Fin k) (L : Finset ℕ) :
    (hmt_paddedList j L).card = L.card + 2 := by
  have hj := j.isLt
  have hnot (b : Bool) : hmt_color j b ∉ L.image (fun c => c + 2 * k) := by
    intro h
    obtain ⟨c, _, he⟩ := Finset.mem_image.mp h
    cases b <;> simp [hmt_color] at he <;> omega
  have hne : hmt_color j false ≠ hmt_color j true := by simp [hmt_color]
  rw [hmt_paddedList, Finset.card_insert_of_notMem (by simpa using And.intro hne (hnot false)),
    Finset.card_insert_of_notMem (hnot true), Finset.card_image_of_injective]
  exact fun _ _ h => Nat.add_right_cancel h

private def hmt_wordList {k : ℕ} (pick : Fin k → Bool) : Finset ℕ :=
  Finset.univ.image fun j => hmt_color j (pick j)

private lemma hmt_wordList_card {k : ℕ} (pick : Fin k → Bool) :
    (hmt_wordList pick).card = k := by
  have hinj : Function.Injective (fun j : Fin k => hmt_color j (pick j)) := by
    intro j l h
    have hj : (pick j).toNat ≤ 1 := by cases pick j <;> decide
    have hl : (pick l).toNat ≤ 1 := by cases pick l <;> decide
    apply Fin.ext
    change 2 * j.val + (pick j).toNat = 2 * l.val + (pick l).toNat at h
    omega
  rw [hmt_wordList, Finset.card_image_of_injective _ hinj]
  simp

end OMA

theorem OMA.solution : type_of% @Erdos629.erdos_629.variants.hmt_recursion := by
  intro k hk
  obtain ⟨oldSide, oldList, hOldSize, hOldBad⟩ := hmt_old_obstruction (k - 2)
  let V := (Fin k × Fin (Erdos629.n (k - 2))) ⊕ (Fin k → Bool)
  let side : V → Bool := Sum.elim (fun jv => oldSide jv.2) OMA.ER629HMT.hmt_wordSide
  let lists : V → Finset ℕ := Sum.elim (fun jv => OMA.hmt_paddedList jv.1 (oldList jv.2))
    (fun word => OMA.hmt_wordList (OMA.ER629HMT.hmt_wordPick word))
  have hsize : ∀ v, (lists v).card = k := by
    rintro (⟨j, v⟩ | w)
    · change (OMA.hmt_paddedList j (oldList v)).card = k
      rw [OMA.hmt_paddedList_card, hOldSize]
      omega
    · exact OMA.hmt_wordList_card (OMA.ER629HMT.hmt_wordPick w)
  have hbad : ∀ f : ℕ → Bool, ∃ v, ∀ c ∈ lists v, f c ≠ side v := by
    intro f
    obtain ⟨v, hv⟩ := hOldBad (fun c => f (c + 2 * k))
    by_cases hpairs : ∀ j : Fin k, ∃ b : Bool, f (OMA.hmt_color j b) = oldSide v
    · obtain ⟨w, hw⟩ :=
        OMA.ER629HMT.hmt_exists_word (fun j b => f (OMA.hmt_color j b)) (oldSide v) hpairs
      refine ⟨.inr w, ?_⟩
      intro c hc
      change c ∈ OMA.hmt_wordList (OMA.ER629HMT.hmt_wordPick w) at hc
      unfold OMA.hmt_wordList at hc
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
      exact hw j
    · push Not at hpairs
      obtain ⟨j, hj⟩ := hpairs
      refine ⟨.inl (j, v), ?_⟩
      intro c hc
      change c ∈ OMA.hmt_paddedList j (oldList v) at hc
      simp only [OMA.hmt_paddedList, Finset.mem_insert, Finset.mem_image] at hc
      rcases hc with rfl | rfl | ⟨d, hd, rfl⟩
      · exact hj false
      · exact hj true
      · exact hv d hd
  simpa only [V, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool] using OMA.hmt_n_le_of_obstruction k side lists hsize hbad
