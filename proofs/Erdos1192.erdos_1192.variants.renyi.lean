import FormalConjectures.ErdosProblems.«1192»

open Nat Filter Finset
open scoped Asymptotics BigOperators

namespace OMA1192Ren

/-! ## The additive energy of a finite set of naturals -/

/-- Pairs of tuples (indexed by `ι` and `κ`) with entries in `B` and equal sums. -/
noncomputable def PairSetT (B : Finset ℕ) (ι : Type) [Fintype ι] (κ : Type) [Fintype κ] :
    Finset ((ι → ↥B) × (κ → ↥B)) := by
  classical
  exact univ.filter (fun p => ∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ))

/-- The number of such pairs. -/
noncomputable def EgyTT (B : Finset ℕ) (ι : Type) [Fintype ι] (κ : Type) [Fintype κ] : ℕ :=
  (PairSetT B ι κ).card

/-- The `j`-fold additive energy of `B`. -/
noncomputable def Egy (B : Finset ℕ) (j : ℕ) : ℕ := EgyTT B (Fin j) (Fin j)

lemma mem_pairSetT {B : Finset ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    {p : (ι → ↥B) × (κ → ↥B)} :
    p ∈ PairSetT B ι κ ↔ ∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ) := by
  classical
  simp [PairSetT]

lemma card_filter_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q] (h : ∀ a, P a ↔ Q (e a)) :
    (univ.filter P).card = (univ.filter Q).card := by
  classical
  have h1 : (univ.filter P).image e = univ.filter Q := by
    ext b
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).mp ha
    · intro hb
      exact ⟨e.symm b, (h _).mpr (by simpa using hb), by simp⟩
  rw [← h1, card_image_of_injective _ e.injective]

lemma EgyTT_congr {ι ι' κ κ' : Type} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (B : Finset ℕ) (e : ι ≃ ι') (f : κ ≃ κ') : EgyTT B ι κ = EgyTT B ι' κ' := by
  classical
  unfold EgyTT
  refine card_filter_equiv (e := (Equiv.arrowCongr e (Equiv.refl ↥B)).prodCongr
    (Equiv.arrowCongr f (Equiv.refl ↥B)))
    (P := fun p : (ι → ↥B) × (κ → ↥B) => ∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ))
    (Q := fun p : (ι' → ↥B) × (κ' → ↥B) => ∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ)) ?_
  rintro ⟨u, v⟩
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.arrowCongr_apply, Equiv.refl_apply,
    Function.comp_apply]
  have e1 : ∑ i : ι', (u (e.symm i) : ℕ) = ∑ i : ι, (u i : ℕ) :=
    Fintype.sum_equiv e.symm (fun i => (u (e.symm i) : ℕ)) (fun i => (u i : ℕ)) (fun i => rfl)
  have e2 : ∑ i : κ', (v (f.symm i) : ℕ) = ∑ i : κ, (v i : ℕ) :=
    Fintype.sum_equiv f.symm (fun i => (v (f.symm i) : ℕ)) (fun i => (v i : ℕ)) (fun i => rfl)
  rw [e1, e2]

lemma Egy_eq_fin {ι κ : Type} [Fintype ι] [Fintype κ] (B : Finset ℕ) (n m : ℕ)
    (hι : Fintype.card ι = n) (hκ : Fintype.card κ = m) : EgyTT B ι κ = EgyTT B (Fin n) (Fin m) := by
  have e : ι ≃ Fin n := Fintype.equivFinOfCardEq hι
  have f : κ ≃ Fin m := Fintype.equivFinOfCardEq hκ
  exact EgyTT_congr B e f

lemma EgyTT_mono {ι κ : Type} [Fintype ι] [Fintype κ] {B B' : Finset ℕ} (h : B ⊆ B') :
    EgyTT B ι κ ≤ EgyTT B' ι κ := by
  classical
  have key : (PairSetT B ι κ).card ≤ (PairSetT B' ι κ).card := by
    have hsub : (PairSetT B ι κ).image (fun p : (ι → ↥B) × (κ → ↥B) =>
        (Prod.mk (fun i => (⟨(p.1 i : ℕ), h (p.1 i).2⟩ : ↥B'))
          (fun i => (⟨(p.2 i : ℕ), h (p.2 i).2⟩ : ↥B')))) ⊆ PairSetT B' ι κ := by
      intro q hq
      rcases mem_image.mp hq with ⟨p, hp, rfl⟩
      rw [mem_pairSetT] at hp ⊢
      simpa using hp
    have hinj : Function.Injective (fun p : (ι → ↥B) × (κ → ↥B) =>
        (Prod.mk (fun i => (⟨(p.1 i : ℕ), h (p.1 i).2⟩ : ↥B'))
          (fun i => (⟨(p.2 i : ℕ), h (p.2 i).2⟩ : ↥B')))) := by
      rintro ⟨u, v⟩ ⟨u', v'⟩ heq
      simp only [Prod.mk.injEq, funext_iff, Subtype.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      exact Prod.ext (funext fun i => Subtype.ext (h1 i)) (funext fun i => Subtype.ext (h2 i))
    calc (PairSetT B ι κ).card
        = ((PairSetT B ι κ).image _).card := (card_image_of_injective _ hinj).symm
      _ ≤ _ := card_le_card hsub
  exact key

lemma Egy_mono {B B' : Finset ℕ} (h : B ⊆ B') (j : ℕ) : Egy B j ≤ Egy B' j := EgyTT_mono h


/-! ## Position sets -/

/-- The set of positions where the tuple `u` (with entries in `B ∪ {y}`) equals `y`. -/
noncomputable def Spos (B : Finset ℕ) (y j : ℕ) (u : Fin j → ↥(insert y B)) : Finset (Fin j) := by
  classical
  exact univ.filter (fun i => (u i : ℕ) = y)

lemma mem_Spos {B : Finset ℕ} {y j : ℕ} {u : Fin j → ↥(insert y B)} {i : Fin j} :
    i ∈ Spos B y j u ↔ (u i : ℕ) = y := by
  classical
  simp [Spos]

lemma Spos_eq_empty_iff {B : Finset ℕ} {y : ℕ} (hy : y ∉ B) {j : ℕ}
    {u : Fin j → ↥(insert y B)} :
    Spos B y j u = ∅ ↔ ∀ i, (u i : ℕ) ∈ B := by
  constructor
  · intro h i
    have h1 : i ∉ Spos B y j u := by simp [h]
    rw [mem_Spos] at h1
    rcases Finset.mem_insert.mp (u i).2 with h2 | h2
    · exact absurd h2 h1
    · exact h2
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [mem_Spos] at hi
    exact hy (hi ▸ h i)

lemma sum_compl_split {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    ∑ x, f x = ∑ x ∈ s, f x + ∑ x ∈ sᶜ, f x := by
  rw [add_comm, ← Finset.sum_sdiff (Finset.subset_univ s), Finset.compl_eq_univ_sdiff]

/-- A tuple whose `y`-positions are `S` splits its sum as `#S * y` plus the sum off `S`. -/
lemma sum_eq_card_mul_add {B : Finset ℕ} {y j : ℕ} {u : Fin j → ↥(insert y B)}
    {S : Finset (Fin j)} (hS : Spos B y j u = S) :
    ∑ i, (u i : ℕ) = S.card * y + ∑ i ∈ Sᶜ, (u i : ℕ) := by
  have h2 : ∑ i ∈ S, (u i : ℕ) = S.card * y := by
    have h3 : ∀ i ∈ S, (u i : ℕ) = y := by
      intro i hi
      have h4 : i ∈ Spos B y j u := by rw [hS]; exact hi
      rwa [mem_Spos] at h4
    rw [sum_congr rfl h3, sum_const, smul_eq_mul]
  rw [sum_compl_split S (fun i => (u i : ℕ)), h2]

/-! ## Old and new pairs -/

/-- Pairs of tuples in `(B ∪ {y})^j` with equal sums. -/
noncomputable def AllPairs (B : Finset ℕ) (y j : ℕ) :
    Finset ((Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))) :=
  PairSetT (insert y B) (Fin j) (Fin j)

/-- Those pairs all of whose entries lie in `B`. -/
noncomputable def OldPairs (B : Finset ℕ) (y j : ℕ) :
    Finset ((Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))) := by
  classical
  exact (PairSetT (insert y B) (Fin j) (Fin j)).filter
    (fun p => (∀ i, (p.1 i : ℕ) ∈ B) ∧ (∀ i, (p.2 i : ℕ) ∈ B))

/-- Pairs of tuples in `(B ∪ {y})^j` with equal sums having an entry equal to `y`. -/
noncomputable def NewPairs (B : Finset ℕ) (y j : ℕ) :
    Finset ((Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))) := by
  classical
  exact (PairSetT (insert y B) (Fin j) (Fin j)).filter
    (fun p => ¬ ((∀ i, (p.1 i : ℕ) ∈ B) ∧ (∀ i, (p.2 i : ℕ) ∈ B)))

lemma Egy_eq_allPairs (B : Finset ℕ) (y j : ℕ) : Egy (insert y B) j = (AllPairs B y j).card := rfl

lemma mem_allPairs {B : Finset ℕ} {y j : ℕ}
    {p : (Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))} :
    p ∈ AllPairs B y j ↔ ∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ) :=
  mem_pairSetT

lemma mem_oldPairs {B : Finset ℕ} {y j : ℕ}
    {p : (Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))} :
    p ∈ OldPairs B y j ↔ (∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ)) ∧
      (∀ i, (p.1 i : ℕ) ∈ B) ∧ (∀ i, (p.2 i : ℕ) ∈ B) := by
  classical
  unfold OldPairs
  rw [mem_filter, mem_pairSetT]

lemma mem_newPairs {B : Finset ℕ} {y j : ℕ}
    {p : (Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))} :
    p ∈ NewPairs B y j ↔ (∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ)) ∧
      ¬ ((∀ i, (p.1 i : ℕ) ∈ B) ∧ (∀ i, (p.2 i : ℕ) ∈ B)) := by
  classical
  unfold NewPairs
  rw [mem_filter, mem_pairSetT]


lemma card_oldPairs {B : Finset ℕ} {y : ℕ} (hy : y ∉ B) (j : ℕ) :
    (OldPairs B y j).card = Egy B j := by
  classical
  have hmem : ∀ p ∈ OldPairs B y j, (∀ k, (p.1 k : ℕ) ∈ B) ∧ (∀ k, (p.2 k : ℕ) ∈ B) :=
    fun p hp => ⟨(mem_oldPairs.mp hp).2.1, (mem_oldPairs.mp hp).2.2⟩
  unfold Egy EgyTT
  refine card_bij (fun p hp => Prod.mk (fun k => (⟨(p.1 k : ℕ), (hmem p hp).1 k⟩ : ↥B))
    (fun k => (⟨(p.2 k : ℕ), (hmem p hp).2 k⟩ : ↥B))) ?_ ?_ ?_
  · intro p hp
    rw [mem_pairSetT]
    exact (mem_oldPairs.mp hp).1
  · intro p hp q hq heq
    simp only [Prod.mk.injEq, funext_iff, Subtype.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    exact Prod.ext (funext fun k => Subtype.ext (h1 k)) (funext fun k => Subtype.ext (h2 k))
  · intro q hq
    refine ⟨Prod.mk (fun k => (⟨(q.1 k : ℕ), mem_insert_of_mem (q.1 k).2⟩ : ↥(insert y B)))
      (fun k => (⟨(q.2 k : ℕ), mem_insert_of_mem (q.2 k).2⟩ : ↥(insert y B))), ?_, ?_⟩
    · rw [mem_oldPairs]
      exact ⟨by simpa using (mem_pairSetT.mp hq), fun k => (q.1 k).2, fun k => (q.2 k).2⟩
    · simp only [Prod.mk.injEq, funext_iff, Subtype.mk.injEq]

lemma Egy_insert {B : Finset ℕ} {y : ℕ} (hy : y ∉ B) (j : ℕ) :
    Egy (insert y B) j = Egy B j + (NewPairs B y j).card := by
  classical
  have h1 : (AllPairs B y j).card = (OldPairs B y j).card + (NewPairs B y j).card := by
    unfold AllPairs OldPairs NewPairs
    exact (card_filter_add_card_filter_not (s := PairSetT (insert y B) (Fin j) (Fin j))
      (p := fun p : (Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B)) =>
        (∀ i, (p.1 i : ℕ) ∈ B) ∧ (∀ i, (p.2 i : ℕ) ∈ B))).symm
  rw [Egy_eq_allPairs, h1, card_oldPairs hy j]


/-- Pairs of tuples in `(B ∪ {y})^j` with equal sums, with `y`-positions `S` and `T`. -/
noncomputable def Fib (B : Finset ℕ) (y j : ℕ) (S T : Finset (Fin j)) :
    Finset ((Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))) := by
  classical
  exact (PairSetT (insert y B) (Fin j) (Fin j)).filter
    (fun p => Spos B y j p.1 = S ∧ Spos B y j p.2 = T)

lemma mem_Fib {B : Finset ℕ} {y j : ℕ} {S T : Finset (Fin j)}
    {p : (Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B))} :
    p ∈ Fib B y j S T ↔ (∑ i, (p.1 i : ℕ) = ∑ i, (p.2 i : ℕ)) ∧
      Spos B y j p.1 = S ∧ Spos B y j p.2 = T := by
  classical
  unfold Fib
  rw [mem_filter, mem_pairSetT]

/-- The set of pairs of position sets with at least one nonempty. -/
noncomputable def Qset (j : ℕ) : Finset (Finset (Fin j) × Finset (Fin j)) := by
  classical
  exact univ.filter (fun q => q.1 ≠ ∅ ∨ q.2 ≠ ∅)

/-- The set of pairs of position sets of equal nonzero cardinality. -/
noncomputable def Qeq (j : ℕ) : Finset (Finset (Fin j) × Finset (Fin j)) := by
  classical
  exact univ.filter (fun q => q.1.card = q.2.card ∧ q.1 ≠ ∅)

lemma mem_Qset {j : ℕ} {q : Finset (Fin j) × Finset (Fin j)} :
    q ∈ Qset j ↔ q.1 ≠ ∅ ∨ q.2 ≠ ∅ := by
  classical
  simp [Qset]

lemma mem_Qeq {j : ℕ} {q : Finset (Fin j) × Finset (Fin j)} :
    q ∈ Qeq j ↔ q.1.card = q.2.card ∧ q.1 ≠ ∅ := by
  classical
  simp [Qeq]

lemma NewPairs_card_eq_sum {B : Finset ℕ} {y : ℕ} (hy : y ∉ B) (j : ℕ) :
    (NewPairs B y j).card = ∑ q ∈ Qset j, (Fib B y j q.1 q.2).card := by
  classical
  set f : (Fin j → ↥(insert y B)) × (Fin j → ↥(insert y B)) → Finset (Fin j) × Finset (Fin j) :=
    fun p => (Spos B y j p.1, Spos B y j p.2) with hf
  have himage : (NewPairs B y j).image f ⊆ Qset j := by
    intro q hq
    rcases mem_image.mp hq with ⟨p, hp, rfl⟩
    rw [mem_Qset]
    by_contra hc
    push_neg at hc
    exact (mem_newPairs.mp hp).2 ⟨(Spos_eq_empty_iff hy).mp hc.1, (Spos_eq_empty_iff hy).mp hc.2⟩
  have hfib : ∀ q ∈ Qset j,
      (NewPairs B y j).filter (fun p => f p = q) = Fib B y j q.1 q.2 := by
    intro q hq
    ext p
    rw [mem_filter, mem_newPairs, mem_Fib, hf]
    constructor
    · rintro ⟨⟨hsum, _⟩, hq'⟩
      rw [Prod.mk.injEq] at hq'
      exact ⟨hsum, hq'.1, hq'.2⟩
    · rintro ⟨hsum, h1, h2⟩
      refine ⟨⟨hsum, ?_⟩, by rw [Prod.mk.injEq]; exact ⟨h1, h2⟩⟩
      intro hall
      rw [mem_Qset] at hq
      rcases hq with hq | hq
      · exact hq (by rw [← h1]; exact (Spos_eq_empty_iff hy).mpr hall.1)
      · exact hq (by rw [← h2]; exact (Spos_eq_empty_iff hy).mpr hall.2)
  rw [card_eq_sum_card_image (f := f)]
  calc ∑ q ∈ (NewPairs B y j).image f, #{a ∈ NewPairs B y j | f a = q}
      = ∑ q ∈ (NewPairs B y j).image f, (Fib B y j q.1 q.2).card := by
        refine sum_congr rfl ?_
        intro q hq
        rw [hfib q (himage hq)]
    _ = ∑ q ∈ Qset j, (Fib B y j q.1 q.2).card := by
        refine sum_subset himage ?_
        intro q hq hqnot
        have hempty : (NewPairs B y j).filter (fun p => f p = q) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro p hp
          exact hqnot (mem_image.mpr ⟨p, (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩)
        rw [← hfib q hq, hempty, card_empty]


lemma mem_B_of_notMem_Spos {B : Finset ℕ} {y j : ℕ} (hy : y ∉ B) {u : Fin j → ↥(insert y B)}
    {i : Fin j} (hi : i ∉ Spos B y j u) : (u i : ℕ) ∈ B := by
  rw [mem_Spos] at hi
  rcases Finset.mem_insert.mp (u i).2 with h | h
  · exact absurd h hi
  · exact h

lemma sum_compl_eq_coe {B : Finset ℕ} {y j : ℕ} {S : Finset (Fin j)}
    {u : Fin j → ↥(insert y B)} (hS : Spos B y j u = S) :
    ∑ i : ↥Sᶜ, (u i.1 : ℕ) = ∑ i ∈ Sᶜ, (u i : ℕ) :=
  Finset.sum_coe_sort (Sᶜ) (fun i => (u i : ℕ))

/-- The diagonal fibres are bounded by the energy of `B` (inject the restrictions to `Sᶜ`, `Tᶜ`). -/
lemma Fib_card_le_diag {B : Finset ℕ} {y : ℕ} (hy : y ∉ B) {j : ℕ} {S T : Finset (Fin j)}
    (hST : S.card = T.card) : (Fib B y j S T).card ≤ EgyTT B ↥Sᶜ ↥Tᶜ := by
  classical
  rw [← Fintype.card_coe (Fib B y j S T), EgyTT, ← Fintype.card_coe (PairSetT B ↥Sᶜ ↥Tᶜ)]
  refine Fintype.card_le_of_injective (f := fun p : ↥(Fib B y j S T) =>
    (⟨Prod.mk (fun i : ↥Sᶜ => (⟨(p.1.1 i.1 : ℕ), mem_B_of_notMem_Spos hy (by
        rw [(mem_Fib.mp p.2).2.1]; exact Finset.mem_compl.mp i.2)⟩ : ↥B))
      (fun i : ↥Tᶜ => (⟨(p.1.2 i.1 : ℕ), mem_B_of_notMem_Spos hy (by
        rw [(mem_Fib.mp p.2).2.2]; exact Finset.mem_compl.mp i.2)⟩ : ↥B)),
      mem_pairSetT.mpr ?_⟩ : ↥(PairSetT B ↥Sᶜ ↥Tᶜ))) ?_
  · simp only [Subtype.coe_mk]
    rw [sum_compl_eq_coe (mem_Fib.mp p.2).2.1, sum_compl_eq_coe (mem_Fib.mp p.2).2.2]
    have e1 := sum_eq_card_mul_add (mem_Fib.mp p.2).2.1
    have e2 := sum_eq_card_mul_add (mem_Fib.mp p.2).2.2
    have hs := (mem_Fib.mp p.2).1
    rw [e1, e2, ← hST] at hs
    exact Nat.add_left_cancel hs
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ heq
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hv1 : ∀ k : Fin j, p.1 k = p'.1 k := by
      intro k
      by_cases hk : k ∈ S
      · have h1k : (p.1 k : ℕ) = y := by
          have hh : k ∈ Spos B y j p.1 := by rw [(mem_Fib.mp hp).2.1]; exact hk
          rwa [mem_Spos] at hh
        have h2k : (p'.1 k : ℕ) = y := by
          have hh : k ∈ Spos B y j p'.1 := by rw [(mem_Fib.mp hp').2.1]; exact hk
          rwa [mem_Spos] at hh
        exact Subtype.ext (by rw [h1k, h2k])
      · have hh := congrFun h1 ⟨k, Finset.mem_compl.mpr hk⟩
        exact Subtype.ext (by simpa using congrArg (fun x : ↥B => (x : ℕ)) hh)
    have hv2 : ∀ k : Fin j, p.2 k = p'.2 k := by
      intro k
      by_cases hk : k ∈ T
      · have h1k : (p.2 k : ℕ) = y := by
          have hh : k ∈ Spos B y j p.2 := by rw [(mem_Fib.mp hp).2.2]; exact hk
          rwa [mem_Spos] at hh
        have h2k : (p'.2 k : ℕ) = y := by
          have hh : k ∈ Spos B y j p'.2 := by rw [(mem_Fib.mp hp').2.2]; exact hk
          rwa [mem_Spos] at hh
        exact Subtype.ext (by rw [h1k, h2k])
      · have hh := congrFun h2 ⟨k, Finset.mem_compl.mpr hk⟩
        exact Subtype.ext (by simpa using congrArg (fun x : ↥B => (x : ℕ)) hh)
    exact Subtype.ext (Prod.ext (funext hv1) (funext hv2))


/-- The off-diagonal fibres: summing over `y ∈ J` costs only one target pair, since `y` is
determined by the restrictions. -/
lemma Fib_sum_le_nondiag {B : Finset ℕ} {j : ℕ} (J : Finset ℕ) (hJ : ∀ y ∈ J, y ∉ B)
    {S T : Finset (Fin j)} (hST : S.card ≠ T.card) :
    ∑ y ∈ J, (Fib B y j S T).card ≤ B.card ^ (2 * j - S.card - T.card) := by
  classical
  have hs1 : S.card ≤ j := by simpa using Finset.card_le_univ S
  have ht1 : T.card ≤ j := by simpa using Finset.card_le_univ T
  have hexp : (j - S.card) + (j - T.card) ≤ 2 * j - S.card - T.card := by omega
  have hstep1 : Fintype.card ↥(J.sigma (fun y => Fib B y j S T))
      ≤ Fintype.card ((↥Sᶜ → ↥B) × (↥Tᶜ → ↥B)) := by
    refine Fintype.card_le_of_injective (f := fun q : ↥(J.sigma (fun y => Fib B y j S T)) =>
      Prod.mk
        (fun i : ↥Sᶜ => (⟨(q.1.2.1 i.1 : ℕ), mem_B_of_notMem_Spos
          (hJ q.1.1 (Finset.mem_sigma.mp q.2).1) (by
            rw [(mem_Fib.mp (Finset.mem_sigma.mp q.2).2).2.1]
            exact Finset.mem_compl.mp i.2)⟩ : ↥B))
        (fun i : ↥Tᶜ => (⟨(q.1.2.2 i.1 : ℕ), mem_B_of_notMem_Spos
          (hJ q.1.1 (Finset.mem_sigma.mp q.2).1) (by
            rw [(mem_Fib.mp (Finset.mem_sigma.mp q.2).2).2.2]
            exact Finset.mem_compl.mp i.2)⟩ : ↥B))) ?_
    intro a b hab
    obtain ⟨q, hq⟩ := a
    obtain ⟨q', hq'⟩ := b
    obtain ⟨y, u, v⟩ := q
    obtain ⟨y', u', v'⟩ := q'
    obtain ⟨hyq, hpq⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hyq', hpq'⟩ := Finset.mem_sigma.mp hq'
    have hpqm := mem_Fib.mp hpq
    have hpqm' := mem_Fib.mp hpq'
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have hA : (∑ i ∈ Sᶜ, (u i : ℕ)) = ∑ i ∈ Sᶜ, (u' i : ℕ) := by
      rw [← sum_compl_eq_coe hpqm.2.1, ← sum_compl_eq_coe hpqm'.2.1]
      exact congrArg (fun g : ↥Sᶜ → ↥B => ∑ i, (g i : ℕ)) h1
    have hC : (∑ i ∈ Tᶜ, (v i : ℕ)) = ∑ i ∈ Tᶜ, (v' i : ℕ) := by
      rw [← sum_compl_eq_coe hpqm.2.2, ← sum_compl_eq_coe hpqm'.2.2]
      exact congrArg (fun g : ↥Tᶜ → ↥B => ∑ i, (g i : ℕ)) h2
    have hs : S.card * y + (∑ i ∈ Sᶜ, (u i : ℕ)) = T.card * y + ∑ i ∈ Tᶜ, (v i : ℕ) := by
      have e1 := sum_eq_card_mul_add hpqm.2.1
      have e2 := sum_eq_card_mul_add hpqm.2.2
      rw [e1, e2] at hpqm
      exact hpqm.1
    have hs' : S.card * y' + (∑ i ∈ Sᶜ, (u' i : ℕ)) = T.card * y' + ∑ i ∈ Tᶜ, (v' i : ℕ) := by
      have e1 := sum_eq_card_mul_add hpqm'.2.1
      have e2 := sum_eq_card_mul_add hpqm'.2.2
      rw [e1, e2] at hpqm'
      exact hpqm'.1
    rw [← hA, ← hC] at hs'
    have hyy' : y = y' := by
      have h1z : (S.card : ℤ) * (y : ℤ) + ((∑ i ∈ Sᶜ, (u i : ℕ) : ℕ) : ℤ) =
          (T.card : ℤ) * (y : ℤ) + ((∑ i ∈ Tᶜ, (v i : ℕ) : ℕ) : ℤ) := by
        exact_mod_cast hs
      have h2z : (S.card : ℤ) * (y' : ℤ) + ((∑ i ∈ Sᶜ, (u i : ℕ) : ℕ) : ℤ) =
          (T.card : ℤ) * (y' : ℤ) + ((∑ i ∈ Tᶜ, (v i : ℕ) : ℕ) : ℤ) := by
        exact_mod_cast hs'
      have hne : (S.card : ℤ) - (T.card : ℤ) ≠ 0 := by
        have hne' : (S.card : ℤ) ≠ (T.card : ℤ) := by exact_mod_cast hST
        omega
      have key : ((S.card : ℤ) - (T.card : ℤ)) * ((y : ℤ) - (y' : ℤ)) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hne
      · exact_mod_cast (sub_eq_zero.mp h)
    have hsnd : HEq (Prod.mk u v) (Prod.mk u' v') := by
      subst hyy'
      apply heq_of_eq
      have hv1 : ∀ k : Fin j, u k = u' k := by
        intro k
        by_cases hk : k ∈ S
        · have e1 : (u k : ℕ) = y := by
            have hh : k ∈ Spos B y j u := by rw [hpqm.2.1]; exact hk
            rwa [mem_Spos] at hh
          have e2 : (u' k : ℕ) = y := by
            have hh : k ∈ Spos B y j u' := by rw [hpqm'.2.1]; exact hk
            rwa [mem_Spos] at hh
          exact Subtype.ext (by rw [e1, e2])
        · have hh := congrFun h1 ⟨k, Finset.mem_compl.mpr hk⟩
          exact Subtype.ext (by simpa using congrArg (fun x : ↥B => (x : ℕ)) hh)
      have hv2 : ∀ k : Fin j, v k = v' k := by
        intro k
        by_cases hk : k ∈ T
        · have e1 : (v k : ℕ) = y := by
            have hh : k ∈ Spos B y j v := by rw [hpqm.2.2]; exact hk
            rwa [mem_Spos] at hh
          have e2 : (v' k : ℕ) = y := by
            have hh : k ∈ Spos B y j v' := by rw [hpqm'.2.2]; exact hk
            rwa [mem_Spos] at hh
          exact Subtype.ext (by rw [e1, e2])
        · have hh := congrFun h2 ⟨k, Finset.mem_compl.mpr hk⟩
          exact Subtype.ext (by simpa using congrArg (fun x : ↥B => (x : ℕ)) hh)
      exact Prod.ext (funext hv1) (funext hv2)
    exact Subtype.ext (Sigma.ext hyy' hsnd)
  have hstep2 : Fintype.card ((↥Sᶜ → ↥B) × (↥Tᶜ → ↥B))
      = B.card ^ (j - S.card) * B.card ^ (j - T.card) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Finset.card_compl,
      Fintype.card_fin]
  have hstep3 : B.card ^ (j - S.card) * B.card ^ (j - T.card)
      ≤ B.card ^ (2 * j - S.card - T.card) := by
    rw [← Nat.pow_add]
    rcases Nat.eq_zero_or_pos B.card with hB | hB
    · rw [hB, Nat.zero_pow (by omega), Nat.zero_pow (by omega)]
    · exact Nat.pow_le_pow_right hB hexp
  rw [← Finset.card_sigma, ← Fintype.card_coe (J.sigma (fun y => Fib B y j S T))]
  exact le_trans hstep1 (by rw [hstep2]; exact hstep3)


/-- The energy of the diagonal fibre in terms of the energy of `B`. -/
lemma EgyTT_compl {B : Finset ℕ} {j : ℕ} {S T : Finset (Fin j)} (hST : S.card = T.card) :
    EgyTT B ↥Sᶜ ↥Tᶜ = Egy B (j - S.card) := by
  classical
  have hScard : Fintype.card ↥Sᶜ = j - S.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have hTcard : Fintype.card ↥Tᶜ = j - T.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have e : ↥Sᶜ ≃ ↥Tᶜ := Fintype.equivOfCardEq (by rw [hScard, hTcard, hST])
  rw [← EgyTT_congr B (Equiv.refl ↥Sᶜ) e, Egy_eq_fin B (j - S.card) (j - S.card) hScard hScard]
  rfl

lemma mem_Qset_of_mem_Qeq {j : ℕ} {q : Finset (Fin j) × Finset (Fin j)} (hq : q ∈ Qeq j) :
    q ∈ Qset j := by
  rw [mem_Qeq] at hq
  rw [mem_Qset]
  exact Or.inl hq.2

/-- Cardinality of `Qset j` is at most `4^j`. -/
lemma card_Qset_le (j : ℕ) : (Qset j).card ≤ 4 ^ j := by
  classical
  have h1 : (Qset j).card ≤ Fintype.card (Finset (Fin j) × Finset (Fin j)) := Finset.card_le_univ _
  have h2 : Fintype.card (Finset (Fin j) × Finset (Fin j)) = 4 ^ j := by
    simp only [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    rw [← Nat.mul_pow]
  omega

/-- The single-step energy-increase bound. -/
lemma step_sum_le {B J : Finset ℕ} {j : ℕ} (hj : 1 ≤ j) (hJ : ∀ y ∈ J, y ∉ B) :
    ∑ y ∈ J, (Egy (insert y B) j - Egy B j)
      ≤ J.card * (∑ q ∈ Qeq j, Egy B (j - q.1.card)) + 4 ^ j * B.card ^ (2 * j - 1) := by
  classical
  have hsub : Qeq j ⊆ Qset j := fun q hq => mem_Qset_of_mem_Qeq hq
  have hdiff : ∀ y ∈ J, Egy (insert y B) j - Egy B j = (NewPairs B y j).card := by
    intro y hy
    have h := Egy_insert (hJ y hy) j
    omega
  have hnew : ∀ y ∈ J, (NewPairs B y j).card = ∑ q ∈ Qset j, (Fib B y j q.1 q.2).card :=
    fun y hy => NewPairs_card_eq_sum (hJ y hy) j
  -- diagonal part
  have hdiag : ∑ q ∈ Qeq j, ∑ y ∈ J, (Fib B y j q.1 q.2).card
      ≤ ∑ q ∈ Qeq j, J.card * Egy B (j - q.1.card) := by
    refine Finset.sum_le_sum ?_
    intro q hq
    have hqeq := mem_Qeq.mp hq
    calc ∑ y ∈ J, (Fib B y j q.1 q.2).card
        ≤ ∑ y ∈ J, EgyTT B ↥q.1ᶜ ↥q.2ᶜ := by
          refine Finset.sum_le_sum ?_
          intro y hy
          exact Fib_card_le_diag (hJ y hy) hqeq.1
      _ = ∑ _y ∈ J, Egy B (j - q.1.card) := by
          rw [EgyTT_compl hqeq.1]
      _ = J.card * Egy B (j - q.1.card) := by rw [Finset.sum_const, smul_eq_mul]
  -- off-diagonal part
  have hoff : ∑ q ∈ (Qset j \ Qeq j), ∑ y ∈ J, (Fib B y j q.1 q.2).card
      ≤ 4 ^ j * B.card ^ (2 * j - 1) := by
    have hper : ∀ q ∈ (Qset j \ Qeq j), ∑ y ∈ J, (Fib B y j q.1 q.2).card
        ≤ B.card ^ (2 * j - 1) := by
      intro q hq
      rw [Finset.mem_sdiff] at hq
      obtain ⟨hqset, hqnot⟩ := hq
      have hne : q.1.card ≠ q.2.card := by
        intro hc
        apply hqnot
        rw [mem_Qeq]
        refine ⟨hc, ?_⟩
        rw [mem_Qset] at hqset
        rcases hqset with h | h
        · exact h
        · intro hz
          rw [hz, Finset.card_empty] at hc
          exact h (Finset.card_eq_zero.mp hc.symm)
      calc ∑ y ∈ J, (Fib B y j q.1 q.2).card
          ≤ B.card ^ (2 * j - q.1.card - q.2.card) := Fib_sum_le_nondiag J hJ hne
        _ ≤ B.card ^ (2 * j - 1) := by
            have h1 : q.1.card ≤ j := by simpa using Finset.card_le_univ q.1
            have h2 : q.2.card ≤ j := by simpa using Finset.card_le_univ q.2
            have hexp : 2 * j - q.1.card - q.2.card ≤ 2 * j - 1 := by omega
            rcases Nat.eq_zero_or_pos B.card with hB | hB
            · rw [hB, Nat.zero_pow (by omega), Nat.zero_pow (by omega)]
            · exact Nat.pow_le_pow_right hB hexp
    calc ∑ q ∈ (Qset j \ Qeq j), ∑ y ∈ J, (Fib B y j q.1 q.2).card
        ≤ ∑ _q ∈ (Qset j \ Qeq j), B.card ^ (2 * j - 1) := Finset.sum_le_sum hper
      _ = (Qset j \ Qeq j).card * B.card ^ (2 * j - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 4 ^ j * B.card ^ (2 * j - 1) := by
          have hc : (Qset j \ Qeq j).card ≤ 4 ^ j :=
            le_trans (Finset.card_le_card Finset.sdiff_subset) (card_Qset_le j)
          exact Nat.mul_le_mul_right _ hc
  calc ∑ y ∈ J, (Egy (insert y B) j - Egy B j)
      = ∑ y ∈ J, (NewPairs B y j).card := Finset.sum_congr rfl hdiff
    _ = ∑ y ∈ J, ∑ q ∈ Qset j, (Fib B y j q.1 q.2).card := Finset.sum_congr rfl hnew
    _ = ∑ q ∈ Qset j, ∑ y ∈ J, (Fib B y j q.1 q.2).card := Finset.sum_comm
    _ = ∑ q ∈ (Qset j \ Qeq j), ∑ y ∈ J, (Fib B y j q.1 q.2).card
          + ∑ q ∈ Qeq j, ∑ y ∈ J, (Fib B y j q.1 q.2).card := by
        rw [Finset.sum_sdiff hsub]
    _ ≤ 4 ^ j * B.card ^ (2 * j - 1) + ∑ q ∈ Qeq j, J.card * Egy B (j - q.1.card) :=
        Nat.add_le_add hoff hdiag
    _ = J.card * (∑ q ∈ Qeq j, Egy B (j - q.1.card)) + 4 ^ j * B.card ^ (2 * j - 1) := by
        rw [Finset.mul_sum]; ring


lemma Egy_zero (B : Finset ℕ) : Egy B 0 = 1 := by
  classical
  have h : PairSetT B (Fin 0) (Fin 0) = univ := by
    apply Finset.eq_univ_of_forall
    intro p
    rw [mem_pairSetT]
    simp
  unfold Egy EgyTT
  rw [h, Finset.card_univ]
  simp

/-! ## The constants -/

/-- The recursively defined constants. -/
noncomputable def Ccoef (r : ℕ) : ℕ → ℕ :=
  fun j => Nat.strongRecOn j (fun j ih =>
    if h : j = 0 then 1
    else r * ((Qeq j).attach.sum (fun q => ih (j - q.1.1.card) (by
      have hq := mem_Qeq.mp q.2
      have hpos : 0 < q.1.1.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hq.2)
      omega)) + 2 * 4 ^ j))

/-- The diagonal coefficient sum (attached form). -/
noncomputable def DsumC (r j : ℕ) : ℕ := (Qeq j).attach.sum (fun q => Ccoef r (j - q.1.1.card))

lemma DsumC_eq_sum (r j : ℕ) : DsumC r j = ∑ q ∈ Qeq j, Ccoef r (j - q.1.card) :=
  Finset.sum_attach (Qeq j) (fun q => Ccoef r (j - q.1.card))

lemma Ccoef_zero (r : ℕ) : Ccoef r 0 = 1 := by
  unfold Ccoef
  rw [Nat.strongRecOn_eq]
  simp

lemma Ccoef_succ (r : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    Ccoef r j = r * (DsumC r j + 2 * 4 ^ j) := by
  unfold Ccoef DsumC
  rw [Nat.strongRecOn_eq]
  rw [dif_neg (by omega : ¬ j = 0)]
  rfl

lemma Ccoef_pos (r : ℕ) (hr : 1 ≤ r) {j : ℕ} (hj : 1 ≤ j) : 0 < Ccoef r j := by
  rw [Ccoef_succ r hj]
  have h4 : 1 ≤ 2 * 4 ^ j := by
    have : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega
  have : 1 * 1 ≤ r * (DsumC r j + 2 * 4 ^ j) :=
    Nat.mul_le_mul hr (by omega)
  omega


lemma pow_le_pow_left_nat {a b : ℕ} (h : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := Nat.pow_le_pow_left h n

/-- One induction step: a good new element exists. -/
lemma exists_good_y (r : ℕ) (hr : 2 ≤ r) {B : Finset ℕ} {t : ℕ} (hcard : B.card = t)
    (hE : ∀ j ∈ Finset.Icc 1 r, Egy B j ≤ Ccoef r j * t ^ j) :
    ∃ y ∈ Finset.Ico ((t + 1) ^ r) (2 * (t + 1) ^ r) \ B,
      ∀ j ∈ Finset.Icc 1 r, Egy (insert y B) j ≤ Ccoef r j * (t + 1) ^ j := by
  classical
  set m := t + 1 with hmdef
  set J := Finset.Ico (m ^ r) (2 * m ^ r) \ B with hJdef
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith
  have hr1 : 1 ≤ r := by omega
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith
  have hJB : ∀ y ∈ J, y ∉ B := by
    intro y hy
    rw [hJdef, Finset.mem_sdiff] at hy
    exact hy.2
  -- cardinality of J
  have hIco : (Finset.Ico (m ^ r) (2 * m ^ r)).card = m ^ r := by
    rw [Nat.card_Ico]
    omega
  have hJcard : m ^ r - t ≤ J.card := by
    rw [hJdef, Finset.card_sdiff]
    have : (B ∩ Finset.Ico (m ^ r) (2 * m ^ r)).card ≤ t := by
      rw [← hcard]
      exact Finset.card_le_card Finset.inter_subset_left
    rw [hIco]
    omega
  have hmr : m ^ r ≤ 2 * J.card := by
    have h2 : 2 * t ≤ m ^ r := by
      have h3 : m ^ 2 ≤ m ^ r := Nat.pow_le_pow_right (by omega) hr
      have h4 : 2 * t ≤ m ^ 2 := by
        rw [hmdef]
        nlinarith [Nat.zero_le t]
      omega
    omega
  have hJpos : 0 < J.card := by
    have : 0 < m ^ r := Nat.pow_pos (by omega)
    omega
  have hJne : J.Nonempty := Finset.card_pos.mp hJpos
  -- the per-j real bound
  have hreal : ∀ j ∈ Finset.Icc 1 r,
      ((∑ y ∈ J, (Egy (insert y B) j - Egy B j) : ℕ) : ℝ)
        ≤ (J.card : ℝ) * ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) / (r : ℝ)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjr : j ≤ r := (Finset.mem_Icc.mp hj).2
    -- diagonal estimate
    have hdiag : (∑ q ∈ Qeq j, Egy B (j - q.1.card)) ≤ DsumC r j * m ^ (j - 1) := by
      rw [DsumC_eq_sum, Finset.sum_mul]
      refine Finset.sum_le_sum (fun q hq => ?_)
      have hqeq := mem_Qeq.mp hq
      have hc1 : q.1.card ≤ j := by simpa using Finset.card_le_univ q.1
      have hcpos : 0 < q.1.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hqeq.2)
      rcases Nat.eq_zero_or_pos (j - q.1.card) with h0 | h0
      · rw [h0, Egy_zero, Ccoef_zero, Nat.one_mul]
        exact Nat.one_le_pow _ _ (by omega)
      · have hmem : j - q.1.card ∈ Finset.Icc 1 r := by
          rw [Finset.mem_Icc]
          omega
        have hIH : Egy B (j - q.1.card) ≤ Ccoef r (j - q.1.card) * t ^ (j - q.1.card) :=
          hE (j - q.1.card) hmem
        have hle : t ^ (j - q.1.card) ≤ m ^ (j - 1) := by
          calc t ^ (j - q.1.card) ≤ m ^ (j - q.1.card) := pow_le_pow_left_nat (by omega) _
            _ ≤ m ^ (j - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        exact le_trans hIH (Nat.mul_le_mul_left _ hle)
    -- off-diagonal estimate
    have hoff : 4 ^ j * B.card ^ (2 * j - 1) ≤ 2 * J.card * (4 ^ j * m ^ (j - 1)) := by
      rw [hcard]
      have h2j : 1 ≤ 2 * j - 1 := by omega
      calc 4 ^ j * t ^ (2 * j - 1) ≤ 4 ^ j * m ^ (2 * j - 1) :=
            Nat.mul_le_mul_left _ (pow_le_pow_left_nat (by omega) _)
        _ = 4 ^ j * (m ^ (j - 1) * m ^ j) := by
            rw [← Nat.pow_add]
            congr 2
            omega
        _ ≤ 4 ^ j * (m ^ (j - 1) * m ^ r) := by
            refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
            exact Nat.pow_le_pow_right (by omega) hjr
        _ ≤ 4 ^ j * (m ^ (j - 1) * (2 * J.card)) := by
            refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmr)
        _ = 2 * J.card * (4 ^ j * m ^ (j - 1)) := by ring
    have hcomb := step_sum_le (B := B) (J := J) hj1 hJB
    have hnat : ∑ y ∈ J, (Egy (insert y B) j - Egy B j)
        ≤ J.card * (DsumC r j * m ^ (j - 1)) + 2 * J.card * (4 ^ j * m ^ (j - 1)) := by
      refine le_trans hcomb (le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hdiag) _) ?_)
      exact Nat.add_le_add_left hoff _
    -- cast to ℝ
    have hcast : ((∑ y ∈ J, (Egy (insert y B) j - Egy B j) : ℕ) : ℝ)
        ≤ (J.card : ℝ) * ((DsumC r j : ℝ) * (m : ℝ) ^ (j - 1))
          + 2 * (J.card : ℝ) * ((4 : ℝ) ^ j * (m : ℝ) ^ (j - 1)) := by
      have h' : ((∑ y ∈ J, (Egy (insert y B) j - Egy B j) : ℕ) : ℝ)
          ≤ ((J.card * (DsumC r j * m ^ (j - 1))
            + 2 * J.card * (4 ^ j * m ^ (j - 1)) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      refine le_trans h' (le_of_eq ?_)
      push_cast
      ring
    have hC : (Ccoef r j : ℝ) = (r : ℝ) * ((DsumC r j : ℝ) + 2 * (4 : ℝ) ^ j) := by
      have h := Ccoef_succ r hj1
      push_cast [h]
      ring
    have hkey : (J.card : ℝ) * ((DsumC r j : ℝ) * (m : ℝ) ^ (j - 1))
        + 2 * (J.card : ℝ) * ((4 : ℝ) ^ j * (m : ℝ) ^ (j - 1))
        = (J.card : ℝ) * ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) / (r : ℝ)) := by
      rw [hC]
      field_simp
    rw [← hkey]
    exact hcast
  -- the summed Δ bound
  have hDelta : (∑ y ∈ J, ∑ j ∈ Finset.Icc 1 r,
      ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) / ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1)))
      ≤ (J.card : ℝ) := by
    rw [Finset.sum_comm]
    have hb : ∀ j ∈ Finset.Icc 1 r, (∑ y ∈ J,
        ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) / ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1)))
        ≤ (J.card : ℝ) / (r : ℝ) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hK : (0 : ℝ) < (Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) := by
        have hp := Ccoef_pos r hr1 hj1
        have hp' : (0 : ℝ) < (Ccoef r j : ℝ) := by exact_mod_cast hp
        have : (0 : ℝ) < (m : ℝ) ^ (j - 1) := pow_pos hmpos _
        exact mul_pos hp' this
      rw [← Finset.sum_div]
      have hsum : ((∑ y ∈ J, (Egy (insert y B) j - Egy B j) : ℕ) : ℝ)
          = ∑ y ∈ J, ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) := by push_cast; ring
      rw [← hsum]
      rw [div_le_div_iff₀ hK hrpos]
      have := hreal j hj
      have hK' : ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) / (r : ℝ)) * (r : ℝ)
          = (Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) := by field_simp
      nlinarith [this, hK']
    calc ∑ j ∈ Finset.Icc 1 r, (∑ y ∈ J,
        ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) / ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1)))
        ≤ ∑ _j ∈ Finset.Icc 1 r, (J.card : ℝ) / (r : ℝ) := Finset.sum_le_sum hb
      _ = (J.card : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
          simp [nsmul_eq_mul]
          field_simp
  -- pigeonhole
  obtain ⟨y, hyJ, hyb⟩ : ∃ y ∈ J, (∑ j ∈ Finset.Icc 1 r,
      ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) / ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1))) ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hlt : (J.card : ℝ) < ∑ y ∈ J, ∑ j ∈ Finset.Icc 1 r,
        ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) / ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1)) := by
      have h1 : (J.card : ℝ) = ∑ _y ∈ J, (1 : ℝ) := by simp
      rw [h1]
      obtain ⟨y0, hy0⟩ := hJne
      exact Finset.sum_lt_sum (fun y hy => (hcon y hy).le) ⟨y0, hy0, hcon y0 hy0⟩
    linarith [hDelta]
  refine ⟨y, hyJ, ?_⟩
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hK : (0 : ℝ) < (Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) := by
    have hp := Ccoef_pos r hr1 hj1
    have hp' : (0 : ℝ) < (Ccoef r j : ℝ) := by exact_mod_cast hp
    have : (0 : ℝ) < (m : ℝ) ^ (j - 1) := pow_pos hmpos _
    exact mul_pos hp' this
  have hnonneg : ∀ j' ∈ Finset.Icc 1 r, 0 ≤
      ((Egy (insert y B) j' - Egy B j' : ℕ) : ℝ) / ((Ccoef r j' : ℝ) * (m : ℝ) ^ (j' - 1)) := by
    intro j' hj'
    have : (0 : ℝ) ≤ ((Egy (insert y B) j' - Egy B j' : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  have hsingle := Finset.single_le_sum hnonneg hj
  have hterm : ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) ≤ (Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) := by
    have h1 : ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) / ((Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1)) ≤ 1 :=
      le_trans hsingle hyb
    rwa [div_le_one hK] at h1
  -- back to ℕ
  have hmono : Egy B j ≤ Egy (insert y B) j := Egy_mono (Finset.subset_insert ..) j
  have hsub : ((Egy (insert y B) j : ℝ)) - (Egy B j : ℝ)
      = ((Egy (insert y B) j - Egy B j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmono]
  have hnatle : Egy (insert y B) j ≤ Egy B j + Ccoef r j * m ^ (j - 1) := by
    have h1 : (Egy (insert y B) j : ℝ) ≤ (Egy B j : ℝ) + (Ccoef r j : ℝ) * (m : ℝ) ^ (j - 1) := by
      have := hterm
      rw [← hsub] at this
      linarith
    have h2 : (Egy (insert y B) j : ℝ) ≤ ((Egy B j + Ccoef r j * m ^ (j - 1) : ℕ) : ℝ) := by
      push_cast
      exact h1
    exact_mod_cast h2
  refine le_trans hnatle ?_
  have h1 : Egy B j ≤ Ccoef r j * t ^ j := hE j hj
  have htj : t ^ j ≤ m ^ j := pow_le_pow_left_nat (by omega) j
  have hstep : t ^ j + m ^ (j - 1) ≤ m ^ j := by
    have hA : t ^ j ≤ t * m ^ (j - 1) := by
      have hpow : t ^ j = t * t ^ (j - 1) := by
        conv_lhs => rw [show j = j - 1 + 1 by omega]
        rw [pow_succ]
        ring
      rw [hpow]
      exact Nat.mul_le_mul_left _ (pow_le_pow_left_nat (by omega) _)
    have hB : m ^ j = m * m ^ (j - 1) := by
      conv_lhs => rw [show j = j - 1 + 1 by omega]
      rw [pow_succ]
      ring
    have hC : t * m ^ (j - 1) + m ^ (j - 1) = m * m ^ (j - 1) := by
      rw [hmdef]
      ring
    omega
  calc Egy B j + Ccoef r j * m ^ (j - 1)
      ≤ Ccoef r j * t ^ j + Ccoef r j * m ^ (j - 1) := Nat.add_le_add_right h1 _
    _ = Ccoef r j * (t ^ j + m ^ (j - 1)) := by ring
    _ ≤ Ccoef r j * m ^ j := Nat.mul_le_mul_left _ hstep
    _ = Ccoef r j * (t + 1) ^ j := by rw [hmdef]

/-! ## The second-moment (energy) inequality -/

/-- The number of `r`-tuples from `B` summing to `n`. -/
noncomputable def FibT (B : Finset ℕ) (r n : ℕ) : ℕ :=
  (univ.filter (fun v : Fin r → ↥B => ∑ i, (v i : ℕ) = n)).card

lemma ncard_fiber_eq (B : Finset ℕ) (r n : ℕ) :
    {v : Fin r → ℕ | (∀ i, v i ∈ (B : Set ℕ)) ∧ ∑ i, v i = n}.ncard = FibT B r n := by
  classical
  set fib : Finset (Fin r → ↥B) := univ.filter (fun v => ∑ i, (v i : ℕ) = n) with hfib
  let e : ↥{v : Fin r → ℕ | (∀ i, v i ∈ (B : Set ℕ)) ∧ ∑ i, v i = n} ≃ ↥fib :=
    { toFun := fun v => ⟨fun i => ⟨(v : Fin r → ℕ) i, v.2.1 i⟩, by
        rw [hfib, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simpa using v.2.2⟩⟩
      invFun := fun w => ⟨fun i => (((w : ↥fib) : Fin r → ↥B) i : ℕ), by
        rw [Set.mem_setOf_eq]
        refine ⟨fun i => (((w : ↥fib) : Fin r → ↥B) i).2, ?_⟩
        have hw := (Finset.mem_filter.mp (w : ↥fib).2).2
        simpa using hw⟩
      left_inv := fun v => by
        refine Subtype.ext (funext fun i => ?_)
        rfl
      right_inv := fun w => by
        refine Subtype.ext (funext fun i => ?_)
        exact Subtype.ext rfl }
  haveI : Fintype ↥{v : Fin r → ℕ | (∀ i, v i ∈ (B : Set ℕ)) ∧ ∑ i, v i = n} :=
    Fintype.ofEquiv _ e.symm
  rw [← Set.fintypeCard_eq_ncard, FibT, ← Fintype.card_coe fib]
  exact Fintype.card_congr e

lemma f_r_le_fibT {A : Set ℕ} {B : Finset ℕ} {r n : ℕ}
    (h : ∀ u ∈ A, u ≤ n → u ∈ (B : Set ℕ)) : Erdos1192.f_r A r n ≤ FibT B r n := by
  classical
  set fib : Finset (Fin r → ↥B) := univ.filter (fun v => ∑ i, (v i : ℕ) = n) with hfib
  have hinj : Function.Injective (fun (v : ↥{v : Fin r → ℕ | (∀ i, v i ∈ A) ∧ ∑ i, v i = n}) =>
      (⟨fun i => ⟨(v : Fin r → ℕ) i, h _ (v.2.1 i) (by
          have hsum := v.2.2
          have hle := Finset.single_le_sum (f := fun i => (v : Fin r → ℕ) i)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
          omega)⟩, by
        rw [hfib, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simpa using v.2.2⟩⟩ : ↥fib)) := by
    intro a b hab
    refine Subtype.ext (funext fun i => ?_)
    exact congrArg Subtype.val (congrFun (congrArg Subtype.val hab) i)
  haveI : Fintype ↥{v : Fin r → ℕ | (∀ i, v i ∈ A) ∧ ∑ i, v i = n} := Fintype.ofInjective _ hinj
  have h1 : Erdos1192.f_r A r n
      = Fintype.card ↥{v : Fin r → ℕ | (∀ i, v i ∈ A) ∧ ∑ i, v i = n} := by
    rw [Erdos1192.f_r, ← Set.fintypeCard_eq_ncard]
  have h2 : FibT B r n = Fintype.card ↥fib := by
    rw [FibT, Fintype.card_coe]
  rw [h1, h2]
  exact Fintype.card_le_of_injective _ hinj

lemma sum_sq_le_egy (B : Finset ℕ) (r x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), (FibT B r n) ^ 2 ≤ Egy B r := by
  classical
  set P := PairSetT B (Fin r) (Fin r) with hP
  set g : ((Fin r → ↥B) × (Fin r → ↥B)) → ℕ := fun p => ∑ i, (p.1 i : ℕ) with hg
  set fib : ℕ → Finset (Fin r → ↥B) :=
    fun n => univ.filter (fun v => ∑ i, (v i : ℕ) = n) with hfib
  have hterm : ∀ n : ℕ, (FibT B r n) ^ 2 ≤ (P.filter (fun p => g p = n)).card := by
    intro n
    have hm : ∀ a ∈ (fib n ×ˢ fib n), a ∈ P.filter (fun p => g p = n) := by
      intro a ha
      rw [Finset.mem_product, hfib, Finset.mem_filter, Finset.mem_filter] at ha
      rw [Finset.mem_filter, mem_pairSetT]
      refine ⟨?_, ?_⟩
      · exact ha.1.2.trans ha.2.2.symm
      · rw [hg]
        exact ha.1.2
    calc (FibT B r n) ^ 2
        = (fib n ×ˢ fib n).card := by
          rw [Finset.card_product, hfib, FibT, sq]
      _ = ((fib n ×ˢ fib n).image id).card := by
          rw [Finset.card_image_of_injective]
          exact fun a b h => h
      _ ≤ _ := Finset.card_le_card (fun a ha => by
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          exact hm b hb)
  have hzero : ∀ n : ℕ, n ∉ P.image g → (P.filter (fun p => g p = n)).card = 0 := by
    intro n hn
    have hempty : P.filter (fun p => g p = n) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [Finset.mem_filter] at hp
      exact hn (hp.2 ▸ Finset.mem_image_of_mem g hp.1)
    rw [hempty, Finset.card_empty]
  have h1 : ∑ n ∈ Finset.range (x + 1), (P.filter (fun p => g p = n)).card
      = ∑ n ∈ Finset.range (x + 1) ∩ P.image g, (P.filter (fun p => g p = n)).card := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro n hn hnot
    exact hzero n (fun hmem => hnot (Finset.mem_inter.mpr ⟨hn, hmem⟩))
  have h2 : ∑ n ∈ Finset.range (x + 1) ∩ P.image g, (P.filter (fun p => g p = n)).card
      ≤ ∑ n ∈ P.image g, (P.filter (fun p => g p = n)).card :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => Nat.zero_le _)
  have h3 : ∑ n ∈ P.image g, (P.filter (fun p => g p = n)).card = P.card :=
    (Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem g hp)).symm
  calc ∑ n ∈ Finset.range (x + 1), (FibT B r n) ^ 2
      ≤ ∑ n ∈ Finset.range (x + 1), (P.filter (fun p => g p = n)).card :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = _ := h1
    _ ≤ _ := h2
    _ = P.card := h3
    _ = Egy B r := rfl


lemma Egy_empty {j : ℕ} (hj : 1 ≤ j) : Egy (∅ : Finset ℕ) j = 0 := by
  classical
  have h : PairSetT (∅ : Finset ℕ) (Fin j) (Fin j) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [mem_pairSetT] at hp
    exact Finset.notMem_empty _ (p.1 ⟨0, hj⟩).2
  unfold Egy EgyTT
  rw [h, Finset.card_empty]

/-- The state of the greedy construction after `t` steps. -/
structure GSt (r : ℕ) where
  B : Finset ℕ
  prev : Finset ℕ
  a : ℕ
  t : ℕ
  hcard : B.card = t
  hprevcard : prev.card = t - 1
  hB : t = 0 ∨ B = insert a prev
  hfresh : t = 0 ∨ a ∉ prev
  hlo : t = 0 ∨ t ^ r ≤ a
  hhi : t = 0 ∨ a < 2 * t ^ r
  henergy : ∀ j ∈ Finset.Icc 1 r, Egy B j ≤ Ccoef r j * t ^ j

noncomputable def GSt.init (r : ℕ) : GSt r where
  B := ∅
  prev := ∅
  a := 0
  t := 0
  hcard := rfl
  hprevcard := rfl
  hB := Or.inl rfl
  hfresh := Or.inl rfl
  hlo := Or.inl rfl
  hhi := Or.inl rfl
  henergy := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [Egy_empty hj1]
    exact Nat.zero_le _

noncomputable def GSt.next (r : ℕ) (hr : 2 ≤ r) (s : GSt r) : GSt r :=
  let h := exists_good_y r hr s.hcard s.henergy
  let y := h.choose
  have hy : y ∈ Finset.Ico ((s.t + 1) ^ r) (2 * (s.t + 1) ^ r) \ s.B := h.choose_spec.1
  have hEn : ∀ j ∈ Finset.Icc 1 r, Egy (insert y s.B) j ≤ Ccoef r j * (s.t + 1) ^ j :=
    h.choose_spec.2
  { B := insert y s.B
    prev := s.B
    a := y
    t := s.t + 1
    hcard := by
      rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hy).2, s.hcard]
    hprevcard := by
      rw [s.hcard]
      omega
    hB := Or.inr rfl
    hfresh := Or.inr (Finset.mem_sdiff.mp hy).2
    hlo := Or.inr (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hy).1).1
    hhi := Or.inr (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hy).1).2
    henergy := hEn }

noncomputable def St (r : ℕ) (hr : 2 ≤ r) : ℕ → GSt r :=
  fun n => Nat.recOn n (GSt.init r) (fun _ s => GSt.next r hr s)

noncomputable def bb (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : ℕ := (St r hr n).a
noncomputable def BB (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : Finset ℕ := (St r hr n).B

lemma St_t (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : (St r hr n).t = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : St r hr (n + 1) = GSt.next r hr (St r hr n) := rfl
      rw [h]
      show (St r hr n).t + 1 = n + 1
      rw [ih]

lemma BB_succ_eq (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    BB r hr (n + 1) = insert (bb r hr (n + 1)) (BB r hr n) := by
  have h := (St r hr (n + 1)).hB
  rcases h with h | h
  · rw [St_t r hr (n + 1)] at h
    omega
  · exact h

lemma BB_card (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : (BB r hr n).card = n := by
  have h := (St r hr n).hcard
  rw [St_t r hr n] at h
  exact h

lemma bb_fresh (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : bb r hr (n + 1) ∉ BB r hr n := by
  have h := (St r hr (n + 1)).hfresh
  rcases h with h | h
  · rw [St_t r hr (n + 1)] at h
    omega
  · exact h

lemma bb_lo (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : (n + 1) ^ r ≤ bb r hr (n + 1) := by
  have h := (St r hr (n + 1)).hlo
  rcases h with h | h
  · rw [St_t r hr (n + 1)] at h
    omega
  · rw [St_t r hr (n + 1)] at h
    exact h

lemma bb_hi (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : bb r hr (n + 1) < 2 * (n + 1) ^ r := by
  have h := (St r hr (n + 1)).hhi
  rcases h with h | h
  · rw [St_t r hr (n + 1)] at h
    omega
  · rw [St_t r hr (n + 1)] at h
    exact h

lemma BB_energy (r : ℕ) (hr : 2 ≤ r) (n j : ℕ) (hj : j ∈ Finset.Icc 1 r) :
    Egy (BB r hr n) j ≤ Ccoef r j * n ^ j := by
  have h := (St r hr n).henergy j hj
  rw [St_t r hr n] at h
  exact h

lemma BB_mono (r : ℕ) (hr : 2 ≤ r) {s t : ℕ} (hst : s ≤ t) : BB r hr s ⊆ BB r hr t := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ t hst ih =>
      refine Finset.Subset.trans ih ?_
      rw [BB_succ_eq]
      exact Finset.subset_insert _ _

lemma bb_mem (r : ℕ) (hr : 2 ≤ r) (n : ℕ) : bb r hr (n + 1) ∈ BB r hr (n + 1) := by
  rw [BB_succ_eq]
  exact Finset.mem_insert_self _ _

lemma bb_inj (r : ℕ) (hr : 2 ≤ r) {s t : ℕ} (hs : 1 ≤ s) (hst : s < t) :
    bb r hr s ≠ bb r hr t := by
  intro heq
  have hmem : bb r hr t ∈ BB r hr (t - 1) := by
    have h1 : bb r hr s ∈ BB r hr s := by
      have := bb_mem r hr (s - 1)
      rwa [Nat.sub_add_cancel hs] at this
    have h2 : BB r hr s ⊆ BB r hr (t - 1) := BB_mono r hr (by omega)
    have h3 := h2 h1
    rw [heq] at h3
    exact h3
  have hnot := bb_fresh r hr (t - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at hnot
  exact hnot hmem


/-! ## The final construction -/

open scoped Classical in
theorem solution_aux (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : Set ℕ,
      ((fun (x : ℕ) ↦ ∑ n ∈ range (x + 1), (Erdos1192.f_r A r n : ℝ) ^ 2) =O[atTop]
        (fun (x : ℕ) ↦ (x : ℝ))) ∧
      ((fun (x : ℕ) ↦ (x : ℝ) ^ (1 / (r : ℝ))) =O[atTop]
        (fun (x : ℕ) ↦ (count (· ∈ A) x : ℝ))) := by
  classical
  refine ⟨{n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n}, ?_, ?_⟩
  · -- the energy bound
    refine Asymptotics.IsBigO.of_bound (Ccoef r r : ℝ) ?_
    filter_upwards with x
    set T := Nat.findGreatest (fun t => t ^ r ≤ x) x with hTdef
    have hx0 : 0 ≤ x := Nat.zero_le x
    have hP0 : (0 : ℕ) ^ r ≤ x := by
      rw [Nat.zero_pow (by omega)]
      exact hx0
    have hTle : T ^ r ≤ x := by
      have := Nat.findGreatest_spec (P := fun t => t ^ r ≤ x) hx0 hP0
      simpa [hTdef] using this
    have hTmax : ∀ t : ℕ, T < t → t ≤ x → ¬ t ^ r ≤ x := by
      intro t ht htx
      exact (Nat.findGreatest_eq_iff (P := fun t => t ^ r ≤ x) (k := x) (m := T)).1
        hTdef.symm |>.2.2 ht htx
    have hfr : ∀ n ≤ x, Erdos1192.f_r {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n} r n
        ≤ FibT (BB r hr T) r n := by
      intro n hn
      refine f_r_le_fibT (fun u hu hux => ?_)
      obtain ⟨t, ht1, rfl⟩ := hu
      have htr : t ^ r ≤ bb r hr t := by
        have := bb_lo r hr (t - 1)
        rwa [Nat.sub_add_cancel ht1] at this
      have htpow : t ≤ t ^ r := Nat.le_self_pow (by omega) t
      have htT : t ≤ T := Nat.le_findGreatest (by omega) (by omega)
      have hmem : bb r hr t ∈ BB r hr t := by
        have := bb_mem r hr (t - 1)
        rwa [Nat.sub_add_cancel ht1] at this
      exact BB_mono r hr htT hmem
    have hb1 : ∑ n ∈ Finset.range (x + 1),
        (Erdos1192.f_r {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n} r n : ℝ) ^ 2
        ≤ ((∑ n ∈ Finset.range (x + 1), (FibT (BB r hr T) r n) ^ 2 : ℕ) : ℝ) := by
      push_cast
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hnx : n ≤ x := by
        rw [Finset.mem_range] at hn
        omega
      have h1 := hfr n hnx
      have h1' : (Erdos1192.f_r {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n} r n : ℝ)
          ≤ (FibT (BB r hr T) r n : ℝ) := by exact_mod_cast h1
      have h2 : (0 : ℝ) ≤ (Erdos1192.f_r {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n} r n : ℝ) :=
        Nat.cast_nonneg _
      nlinarith [h1', h2]
    have hb2 : ((∑ n ∈ Finset.range (x + 1), (FibT (BB r hr T) r n) ^ 2 : ℕ) : ℝ)
        ≤ ((Ccoef r r * x : ℕ) : ℝ) := by
      have h2 : ((∑ n ∈ Finset.range (x + 1), (FibT (BB r hr T) r n) ^ 2 : ℕ) : ℝ)
          ≤ ((Egy (BB r hr T) r : ℕ) : ℝ) := by
        exact_mod_cast sum_sq_le_egy (BB r hr T) r x
      have h3 : ((Egy (BB r hr T) r : ℕ) : ℝ) ≤ ((Ccoef r r * T ^ r : ℕ) : ℝ) := by
        have := BB_energy r hr T r (by rw [Finset.mem_Icc]; omega)
        exact_mod_cast this
      have h4 : ((Ccoef r r * T ^ r : ℕ) : ℝ) ≤ ((Ccoef r r * x : ℕ) : ℝ) := by
        have hp : ((T ^ r : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hTle
        have hc : (0 : ℝ) ≤ (Ccoef r r : ℝ) := Nat.cast_nonneg _
        have : (Ccoef r r : ℝ) * (T ^ r : ℕ) ≤ (Ccoef r r : ℝ) * (x : ℝ) := by nlinarith
        calc ((Ccoef r r * T ^ r : ℕ) : ℝ) = (Ccoef r r : ℝ) * (T ^ r : ℕ) := by push_cast; ring
          _ ≤ (Ccoef r r : ℝ) * (x : ℝ) := this
          _ = ((Ccoef r r * x : ℕ) : ℝ) := by push_cast; ring
      calc ((∑ n ∈ Finset.range (x + 1), (FibT (BB r hr T) r n) ^ 2 : ℕ) : ℝ)
          ≤ ((Egy (BB r hr T) r : ℕ) : ℝ) := h2
        _ ≤ ((Ccoef r r * T ^ r : ℕ) : ℝ) := h3
        _ ≤ ((Ccoef r r * x : ℕ) : ℝ) := h4
    have hb3 : ((Ccoef r r * x : ℕ) : ℝ) = (Ccoef r r : ℝ) * (x : ℝ) := by push_cast; ring
    have hnn : (0 : ℝ) ≤ ∑ n ∈ Finset.range (x + 1),
        (Erdos1192.f_r {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n} r n : ℝ) ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg hnn, abs_of_nonneg (Nat.cast_nonneg x)]
    calc ∑ n ∈ Finset.range (x + 1),
        (Erdos1192.f_r {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n} r n : ℝ) ^ 2
        ≤ ((∑ n ∈ Finset.range (x + 1), (FibT (BB r hr T) r n) ^ 2 : ℕ) : ℝ) := hb1
      _ ≤ ((Ccoef r r * x : ℕ) : ℝ) := hb2
      _ = (Ccoef r r : ℝ) * (x : ℝ) := hb3
  · -- the counting bound
    refine Asymptotics.IsBigO.of_bound 4 ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    set T := Nat.findGreatest (fun t => 2 * t ^ r ≤ x) x with hTdef
    have hx0 : 0 ≤ x := Nat.zero_le x
    have hP0 : 2 * (0 : ℕ) ^ r ≤ x := by
      rw [Nat.zero_pow (by omega)]
      omega
    have hTle : 2 * T ^ r ≤ x := by
      have := Nat.findGreatest_spec (P := fun t => 2 * t ^ r ≤ x) hx0 hP0
      simpa [hTdef] using this
    have hTmax : ∀ t : ℕ, T < t → t ≤ x → ¬ 2 * t ^ r ≤ x := by
      intro t ht htx
      exact (Nat.findGreatest_eq_iff (P := fun t => 2 * t ^ r ≤ x) (k := x) (m := T)).1
        hTdef.symm |>.2.2 ht htx
    have hT1 : 1 ≤ T := by
      have h1 : 2 * (1 : ℕ) ^ r ≤ x := by simpa using hx
      exact Nat.le_findGreatest (by omega) h1
    have hTx : T ≤ x := Nat.findGreatest_le x
    have hTlt : T < x := by
      rcases Nat.lt_or_ge T x with h | h
      · exact h
      · exfalso
        have hTp : T ≤ T ^ r := Nat.le_self_pow (by omega) T
        have h2 : 2 * T ≤ x := by omega
        have h3 : 2 * T ^ r ≤ x := hTle
        omega
    -- the injection into the counted set
    have hcount : T ≤ count (· ∈ {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n}) x := by
      rw [Nat.count_eq_card_filter_range]
      have himg : ((Finset.Ico 1 (T + 1)).image (bb r hr)).card = (Finset.Ico 1 (T + 1)).card := by
        refine Finset.card_image_of_injOn ?_
        intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_Ico] at ha hb
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact bb_inj r hr (by omega) h hab
        · exact bb_inj r hr (by omega) h hab.symm
      have hsub : (Finset.Ico 1 (T + 1)).image (bb r hr) ⊆
          (Finset.range x).filter (· ∈ {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n}) := by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
        rw [Finset.mem_Ico] at ht
        obtain ⟨ht1, htT⟩ := ht
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · have htt : t ≤ T := Nat.lt_succ_iff.mp htT
          have hhi := bb_hi r hr (t - 1)
          rw [Nat.sub_add_cancel ht1] at hhi
          have hmono : 2 * t ^ r ≤ 2 * T ^ r :=
            Nat.mul_le_mul_left 2 (pow_le_pow_left_nat htt r)
          omega
        · exact ⟨t, ht1, rfl⟩
      calc T = (Finset.Ico 1 (T + 1)).card := by rw [Nat.card_Ico]; omega
        _ = ((Finset.Ico 1 (T + 1)).image (bb r hr)).card := himg.symm
        _ ≤ ((Finset.range x).filter (· ∈ {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n})).card :=
              Finset.card_le_card hsub
    -- the real bound
    have hx4 : x ≤ (4 * T) ^ r := by
      have hlt : x < 2 * (T + 1) ^ r := by
        have := hTmax (T + 1) (by omega) (by omega)
        omega
      have h2 : (T + 1) ^ r ≤ (2 * T) ^ r := Nat.pow_le_pow_left (by omega) r
      have h4 : 2 ^ (r + 1) ≤ 4 ^ r := by
        have h5 : (4 : ℕ) ^ r = 2 ^ (2 * r) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
        rw [h5]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      calc x ≤ 2 * (T + 1) ^ r := by omega
        _ ≤ 2 * (2 * T) ^ r := Nat.mul_le_mul_left 2 h2
        _ = 2 ^ (r + 1) * T ^ r := by rw [mul_pow, pow_succ]; ring
        _ ≤ 4 ^ r * T ^ r := Nat.mul_le_mul_right _ h4
        _ = (4 * T) ^ r := by rw [mul_pow]
    have hreal : (x : ℝ) ≤ (((4 * T : ℕ) : ℝ)) ^ r := by
      exact_mod_cast hx4
    have hstep : ((((4 * T : ℕ) : ℝ)) ^ r) ^ (1 / (r : ℝ)) = (((4 * T : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      have hrne : (r : ℝ) ≠ 0 := by positivity
      rw [mul_one_div, div_self hrne, Real.rpow_one]
    have hkey : (x : ℝ) ^ (1 / (r : ℝ)) ≤ ((4 * T : ℕ) : ℝ) := by
      calc (x : ℝ) ^ (1 / (r : ℝ)) ≤ ((((4 * T : ℕ) : ℝ)) ^ r) ^ (1 / (r : ℝ)) :=
            Real.rpow_le_rpow (Nat.cast_nonneg x) hreal (by positivity)
        _ = (((4 * T : ℕ) : ℝ)) := hstep
    have hTcount : ((T : ℕ) : ℝ) ≤ (count (· ∈ {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n}) x : ℝ) := by
      exact_mod_cast hcount
    have hfin : (x : ℝ) ^ (1 / (r : ℝ))
        ≤ 4 * (count (· ∈ {n : ℕ | ∃ t : ℕ, 1 ≤ t ∧ bb r hr t = n}) x : ℝ) := by
      have h4T : ((4 * T : ℕ) : ℝ) = 4 * (T : ℝ) := by push_cast; ring
      rw [h4T] at hkey
      nlinarith [hTcount]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _), abs_of_nonneg (Nat.cast_nonneg _)]
    exact hfin


end OMA1192Ren

open scoped Classical in
theorem OMA.solution : type_of% @Erdos1192.erdos_1192.variants.renyi :=
  OMA1192Ren.solution_aux
