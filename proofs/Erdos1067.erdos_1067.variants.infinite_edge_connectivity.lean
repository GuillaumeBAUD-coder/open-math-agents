import FormalConjectures.ErdosProblems.«1067»
import Mathlib.Order.TransfiniteIteration

/-!
# Infinite edge connectivity in an uncountably chromatic graph

The finite-cut descent and countable restoration follow Thomassen,
*Infinitely connected subgraphs in graphs of uncountable chromatic number*,
Combinatorica 37 (2017), with restoration dependencies tracked by the
endpoints of the previously restored cuts.
-/

/- Descending finite cuts and the resulting edge connectivity. -/

namespace ThomassenDescent

open SimpleGraph Set

universe u

variable {V : Type u}

/-- Every edge remains connecting its endpoints after any finite edge deletion. -/
def RobustEdges (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → ∀ S : Set (Sym2 V), S.Finite → (G.deleteEdges S).Reachable x y

/-- An edge set eligible for a step of the finite-cut process. -/
def FiniteCut (G E : SimpleGraph V) : Prop :=
  E ≤ G ∧ E.edgeSet.Finite ∧ E ≠ ⊥ ∧
    ∀ ⦃x y⦄, E.Adj x y → ¬ (G \ E).Reachable x y

private def crossing (G : SimpleGraph V) (W : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬ (x ∈ W ↔ y ∈ W)
  symm := ⟨fun _ _ h => ⟨h.1.symm,fun h' => h.2 h'.symm⟩⟩
  loopless := ⟨fun _ h => h.2 Iff.rfl⟩

private lemma reachable_preserves_side {G : SimpleGraph V} {W : Set V}
    (hPres : ∀ ⦃x y⦄, G.Adj x y → (x ∈ W ↔ y ∈ W)) {x y : V}
    (h : G.Reachable x y) : x ∈ W ↔ y ∈ W := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hPres h).trans ih

private lemma finiteCut_of_bad_edge {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y)
    {S : Set (Sym2 V)} (hS : S.Finite) (hBad : ¬ (G.deleteEdges S).Reachable x y) :
    ∃ E, FiniteCut G E := by
  classical
  let W : Set V := {z | (G.deleteEdges S).Reachable x z}
  let E := crossing G W
  have hWadj {a b : V} (h : (G.deleteEdges S).Adj a b) : a ∈ W ↔ b ∈ W :=
    ⟨fun h' => h'.trans h.reachable, fun h' => h'.trans h.symm.reachable⟩
  have hcut : E.edgeSet ⊆ S := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have h : G.Adj a b ∧ ¬ (a ∈ W ↔ b ∈ W) := (E.mem_edgeSet).mp he
      by_contra hn
      exact h.2 (hWadj (deleteEdges_adj.mpr ⟨h.1,hn⟩))
  have hE : E.Adj x y := ⟨hxy,fun h => hBad (h.mp Reachable.rfl)⟩
  refine ⟨E,fun _ _ h => h.1, hS.subset hcut, (fun h => ?_), ?_⟩
  · rw [h] at hE
    exact hE
  · intro a b h hRe
    apply h.2
    apply reachable_preserves_side _ hRe
    intro v w hvw
    obtain ⟨hG,hNot⟩ := (sdiff_adj G E v w).mp hvw
    by_contra hc
    exact hNot ⟨hG,hc⟩

theorem robust_of_no_cut (G : SimpleGraph V) (h : ¬ ∃ E, FiniteCut G E) :
    RobustEdges G := by
  intro x y hxy S hS
  by_contra hBad
  exact h (finiteCut_of_bad_edge hxy hS hBad)

private noncomputable def chosenCut (G : SimpleGraph V) : SimpleGraph V := by
  classical
  exact if h : ∃ E, FiniteCut G E then Classical.choose h else ⊥

private lemma chosenCut_properties (G : SimpleGraph V) :
    chosenCut G ≤ G ∧ (chosenCut G).edgeSet.Finite ∧
      ∀ ⦃x y⦄, (chosenCut G).Adj x y → ¬ (G \ chosenCut G).Reachable x y := by
  classical
  unfold chosenCut
  split_ifs with h
  · have hs := Classical.choose_spec h
    exact ⟨hs.1,hs.2.1,hs.2.2.2⟩
  · simp

private noncomputable def deleteStep (G : (SimpleGraph V)ᵒᵈ) : (SimpleGraph V)ᵒᵈ :=
  OrderDual.toDual (OrderDual.ofDual G \ chosenCut (OrderDual.ofDual G))

private noncomputable def descend (G : SimpleGraph V) (i : Ordinal.{u}) : SimpleGraph V :=
  OrderDual.ofDual (transfiniteIterate deleteStep i (OrderDual.toDual G))

private lemma descend_zero (G : SimpleGraph V) : descend G 0 = G := by
  simp only [descend, ← Ordinal.bot_eq_zero, transfiniteIterate_bot, OrderDual.ofDual_toDual]

private lemma descend_succ (G : SimpleGraph V) (i : Ordinal.{u}) :
    descend G (Order.succ i) = descend G i \ chosenCut (descend G i) := by
  simp only [descend, transfiniteIterate_succ _ _ _ (not_isMax i), deleteStep,
    OrderDual.ofDual_toDual]

private lemma descend_limit (G : SimpleGraph V) (i : Ordinal.{u}) (hi : Order.IsSuccLimit i) :
    descend G i = ⨅ j : Iio i, descend G j.val := by
  simp only [descend, transfiniteIterate_limit _ _ _ hi, ofDual_iSup]

private lemma descend_anti (G : SimpleGraph V) : Antitone (descend G) := by
  have hStep (K : (SimpleGraph V)ᵒᵈ) : K ≤ deleteStep K := by
    change OrderDual.toDual (OrderDual.ofDual K) ≤ OrderDual.toDual
      (OrderDual.ofDual K \ chosenCut (OrderDual.ofDual K))
    exact OrderDual.toDual_le_toDual.mpr sdiff_le
  intro i j hij
  exact OrderDual.ofDual_le_ofDual.mpr
    ((monotone_transfiniteIterate (J := Ordinal.{u}) deleteStep (OrderDual.toDual G) hStep) hij)

private lemma descend_le (G : SimpleGraph V) (i : Ordinal.{u}) : descend G i ≤ G := by
  calc
    descend G i ≤ descend G 0 :=
      descend_anti G (by simpa only [Ordinal.bot_eq_zero] using (bot_le : (⊥ : Ordinal.{u}) ≤ i))
    _ = G := descend_zero G

private lemma exists_stationary (G : SimpleGraph V) :
    ∃ i : Ordinal.{u}, descend G (Order.succ i) = descend G i := by
  have h : ∃ i j : Ordinal.{u}, i < j ∧ descend G i = descend G j := by
    obtain ⟨a,b,heq,hne⟩ := Function.not_injective_iff.mp (not_injective_of_ordinal (descend G))
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact ⟨a,b,hab,heq⟩
    · exact ⟨b,a,hba,heq.symm⟩
  obtain ⟨i,j,hij,heq⟩ := h
  refine ⟨i,le_antisymm (descend_anti G (Order.le_succ i)) ?_⟩
  rw [heq]
  exact descend_anti G (Order.succ_le_of_lt hij)

private lemma stationary_robust (G : SimpleGraph V) {i : Ordinal.{u}}
    (hStat : descend G (Order.succ i) = descend G i) : RobustEdges (descend G i) := by
  apply robust_of_no_cut
  intro h
  have hc : FiniteCut (descend G i) (chosenCut (descend G i)) := by
    classical
    simp only [chosenCut, dif_pos h]
    exact Classical.choose_spec h
  rw [descend_succ] at hStat
  have hDis := sdiff_eq_left.mp hStat
  exact hc.2.2.1 ((disjoint_iff_inf_le.mp hDis) |> fun hh => le_bot_iff.mp (le_trans (le_inf hc.1 le_rfl) hh))

private lemma removed_at_stage (G : SimpleGraph V) {x y : V} (hG : G.Adj x y) (i : Ordinal.{u})
    (hNot : ¬ (descend G i).Adj x y) :
    ∃ j : Ordinal.{u}, j < i ∧ (chosenCut (descend G j)).Adj x y := by
  induction i using SuccOrder.limitRecOn with
  | isMin i hi =>
    rw [hi.eq_bot] at hNot
    exact (hNot (by simpa only [show (⊥ : Ordinal.{u}) = 0 from rfl, descend_zero] using hG)).elim
  | succ i hi ih =>
    have hlt := Order.lt_succ_of_not_isMax hi
    by_cases hadj : (descend G i).Adj x y
    · refine ⟨i,hlt,?_⟩
      by_contra hc
      exact hNot (by rw [descend_succ]; exact (sdiff_adj _ _ _ _).mpr ⟨hadj,hc⟩)
    · obtain ⟨j,hj,hE⟩ := ih hadj
      exact ⟨j,hj.trans hlt,hE⟩
  | isSuccLimit i hi ih =>
    have hOld : ∃ j : Iio i, ¬ (descend G j.val).Adj x y := by
      by_contra! hall
      apply hNot
      rw [descend_limit G i hi]
      exact iInf_adj.mpr ⟨hall,hG.ne⟩
    obtain ⟨j,hj⟩ := hOld
    obtain ⟨k,hk,hE⟩ := ih j.val j.property hj
    exact ⟨k,hk.trans j.property,hE⟩

/-- A transfinite sequence of finite cuts ending in a graph with robust edges. -/
theorem exists_sequence (G : SimpleGraph V) :
    ∃ (a : Ordinal.{u}) (H : SimpleGraph V) (K L E : Iio a → SimpleGraph V),
      H ≤ G ∧ RobustEdges H ∧
      (∀ i, E i ≤ K i ∧ (E i).edgeSet.Finite ∧ L i = K i \ E i ∧
        ∀ ⦃x y⦄, (E i).Adj x y → ¬ (L i).Reachable x y) ∧
      (∀ ⦃i j⦄, i < j → K j ≤ L i) ∧ (∀ i, H ≤ L i) ∧
      G = H ⊔ ⨆ i, E i := by
  obtain ⟨a,ha⟩ := exists_stationary G
  let H := descend G a
  let K (i : Iio a) := descend G i.val
  let E (i : Iio a) := chosenCut (K i)
  let L (i : Iio a) := K i \ E i
  refine ⟨a,H,K,L,E,descend_le G a,stationary_robust G ha,?_,?_,?_,?_⟩
  · intro i
    have h := chosenCut_properties (K i)
    exact ⟨h.1,h.2.1,rfl,h.2.2⟩
  · intro i j hij
    change descend G j.val ≤ descend G i.val \ chosenCut (descend G i.val)
    rw [← descend_succ]
    exact descend_anti G (Order.succ_le_of_lt hij)
  · intro i
    change descend G a ≤ descend G i.val \ chosenCut (descend G i.val)
    rw [← descend_succ]
    exact descend_anti G (Order.succ_le_of_lt i.property)
  · apply le_antisymm
    · intro x y hxy
      apply (sup_adj _ _ _ _).mpr
      by_cases hh : H.Adj x y
      · exact Or.inl hh
      · obtain ⟨j,hj,hE⟩ := removed_at_stage G hxy a hh
        exact Or.inr (iSup_adj.mpr ⟨⟨j,hj⟩,hE⟩)
    · apply sup_le (descend_le G a)
      exact iSup_le fun i => (chosenCut_properties (K i)).1.trans (descend_le G i.val)

end ThomassenDescent

/- An endpoint-based dependency lemma for finite-cut deletion sequences.
See Thomassen, Infinitely connected subgraphs in graphs of uncountable chromatic number,
https://doi.org/10.1007/s00493-016-3436-4, Section 3. -/

namespace ThomassenCuts

open SimpleGraph Set

variable {V : Type*}

private lemma first_restored {H E : SimpleGraph V} {u v : V}
    (p : (H ⊔ E).Walk u v) :
    H.Reachable u v ∨ ∃ w ∈ E.support, H.Reachable u w := by
  induction p with
  | nil => exact Or.inl Reachable.rfl
  | @cons x y z h _ ih =>
    rcases (sup_adj H E x y).mp h with hh | he
    · rcases ih with h | ⟨w,hw,hy⟩
      · exact Or.inl (hh.reachable.trans h)
      · exact Or.inr ⟨w,hw,hh.reachable.trans hy⟩
    · exact Or.inr ⟨x,he.mem_support_left,Reachable.rfl⟩

/-- If a deletion preserves reachability among the endpoints of restored edges, restoring
those edges does not reconnect any previously connected pair separated by the deletion. -/
theorem reachable_of_preserved_endpoints {G H E : SimpleGraph V} (hHG : H ≤ G)
    (hEnds : ∀ x ∈ E.support, ∀ y ∈ E.support, G.Reachable x y → H.Reachable x y)
    {u v : V} (hG : G.Reachable u v) (hRestored : (H ⊔ E).Reachable u v) :
    H.Reachable u v := by
  obtain ⟨p⟩ := hRestored
  rcases first_restored p with h | ⟨x,hx,hux⟩
  · exact h
  rcases first_restored p.reverse with h | ⟨y,hy,hvy⟩
  · exact h.symm
  have hxy := (Reachable.mono hHG hux).symm.trans (hG.trans (Reachable.mono hHG hvy))
  exact hux.trans ((hEnds x hx y hy hxy).trans hvy.symm)

variable {ι : Type*}

private def pairStages (K L : ι → SimpleGraph V) (x y : V) : Set ι :=
  {i | (K i).Reachable x y ∧ ¬ (L i).Reachable x y}

/-- Stages where a pair of vertices in the specified set stops being connected. -/
def splittingStages (K L : ι → SimpleGraph V) (W : Set V) : Set ι :=
  {i | ∃ x ∈ W, ∃ y ∈ W, (K i).Reachable x y ∧ ¬ (L i).Reachable x y}

private lemma splittingStages_eq (K L : ι → SimpleGraph V) (W : Set V) :
    splittingStages K L W = ⋃ x ∈ W, ⋃ y ∈ W, pairStages K L x y := by
  ext i
  simp only [splittingStages, pairStages, mem_ofPred_eq, mem_iUnion, exists_prop]

private lemma pairStages_finite [LinearOrder ι] (K L : ι → SimpleGraph V)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i) (x y : V) :
    (pairStages K L x y).Finite := by
  apply Set.Subsingleton.finite
  intro i hi j hj
  change (K i).Reachable x y ∧ ¬ (L i).Reachable x y at hi
  change (K j).Reachable x y ∧ ¬ (L j).Reachable x y at hj
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hi.2 (Reachable.mono (hOrder hlt) hj.1)
  · exact hj.2 (Reachable.mono (hOrder hgt) hi.1)

/-- Only finitely many stages separate pairs from a fixed finite set of vertices. -/
theorem finite_splittingStages [LinearOrder ι] (K L : ι → SimpleGraph V)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i) {W : Set V} (hW : W.Finite) :
    (splittingStages K L W).Finite := by
  rw [splittingStages_eq]
  exact hW.biUnion fun x _ => hW.biUnion fun y _ => pairStages_finite K L hOrder x y

/-- Only countably many stages separate pairs from a fixed countable set of vertices. -/
theorem countable_splittingStages [LinearOrder ι] (K L : ι → SimpleGraph V)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i) {W : Set V} (hW : W.Countable) :
    (splittingStages K L W).Countable := by
  rw [splittingStages_eq]
  exact hW.biUnion fun x _ => hW.biUnion fun y _ => (pairStages_finite K L hOrder x y).countable

/-- Restoring a graph with finite support can invalidate only finitely many separations. -/
theorem finite_restoration_dependencies [LinearOrder ι] (K L : ι → SimpleGraph V)
    (hLe : ∀ i, L i ≤ K i) (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i)
    {E : SimpleGraph V} (hE : E.support.Finite) :
    {i | ∃ u v, (K i).Reachable u v ∧ ¬ (L i).Reachable u v ∧
      (L i ⊔ E).Reachable u v}.Finite := by
  apply (finite_splittingStages K L hOrder hE).subset
  intro i hi
  obtain ⟨u,v,hG,hH,hRestored⟩ := hi
  by_contra h
  apply hH
  apply reachable_of_preserved_endpoints (hLe i) _ hG hRestored
  intro x hx y hy hxy
  by_contra hxy'
  exact h ⟨x,hx,y,hy,hxy,hxy'⟩

private def stageClosure (K L : ι → SimpleGraph V) (ends : ι → Set V)
    (S : Set ι) : ℕ → Set ι
  | 0 => S
  | n + 1 =>
      let T := stageClosure K L ends S n
      T ∪ splittingStages K L (⋃ i ∈ T, ends i)

/-- A countable seed set of stages extends to a countable set closed under endpoint
separation: every stage that separates two endpoints of selected stages is selected. -/
theorem countable_closed_extension [LinearOrder ι] (K L : ι → SimpleGraph V)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i) (ends : ι → Set V)
    (hEnds : ∀ i, (ends i).Countable) {S : Set ι} (hS : S.Countable) :
    ∃ T : Set ι, S ⊆ T ∧ T.Countable ∧ splittingStages K L (⋃ i ∈ T, ends i) ⊆ T := by
  let step := stageClosure K L ends S
  let T := ⋃ n, step n
  have hStep : Monotone step := by
    apply monotone_nat_of_le_succ
    intro n
    exact subset_union_left
  have hCount (n : ℕ) : (step n).Countable := by
    induction n with
    | zero => exact hS
    | succ n ih =>
      exact ih.union (countable_splittingStages K L hOrder (ih.biUnion fun i _ => hEnds i))
  refine ⟨T, subset_iUnion step 0, countable_iUnion hCount, ?_⟩
  intro i hi
  obtain ⟨x,hx,y,hy,hxy⟩ := hi
  obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
  obtain ⟨k,hk,hyk⟩ := mem_iUnion₂.mp hy
  obtain ⟨n,hjn⟩ := mem_iUnion.mp hj
  obtain ⟨p,hkp⟩ := mem_iUnion.mp hk
  let q := max n p
  have hjq : j ∈ step q := hStep (le_max_left _ _) hjn
  have hkq : k ∈ step q := hStep (le_max_right _ _) hkp
  have hSplit : i ∈ splittingStages K L (⋃ j ∈ step q, ends j) :=
    ⟨x,mem_iUnion₂.mpr ⟨j,hjq,hxj⟩,y,mem_iUnion₂.mpr ⟨k,hkq,hyk⟩,hxy⟩
  exact mem_iUnion.mpr ⟨q + 1,Or.inr hSplit⟩

end ThomassenCuts

namespace ThomassenRestore

open SimpleGraph Set

universe u w

variable {V : Type u} {ι : Type w}

/-- The union of graphs belonging to a set of stages. -/
def restored (E : ι → SimpleGraph V) (S : Set ι) : SimpleGraph V :=
  ⨆ i : S, E i.val

lemma restored_adj_iff (E : ι → SimpleGraph V) (S : Set ι) (x y : V) :
    (restored E S).Adj x y ↔ ∃ i ∈ S, (E i).Adj x y := by
  rw [restored, iSup_adj]
  constructor
  · rintro ⟨⟨i,hi⟩,hxy⟩
    exact ⟨i,hi,hxy⟩
  · rintro ⟨i,hi,hxy⟩
    exact ⟨⟨i,hi⟩,hxy⟩

lemma restored_mono (E : ι → SimpleGraph V) : Monotone (restored E) := by
  intro S T hST x y h
  obtain ⟨i,hi,hxy⟩ := (restored_adj_iff E S x y).mp h
  exact (restored_adj_iff E T x y).mpr ⟨i,hST hi,hxy⟩

private lemma restored_union (E : ι → SimpleGraph V) (S T : Set ι) :
    restored E (S ∪ T) = restored E S ⊔ restored E T := by
  ext x y
  simp only [restored_adj_iff, sup_adj, mem_union]
  constructor
  · rintro ⟨i,hi | hi,h⟩
    · exact Or.inl ⟨i,hi,h⟩
    · exact Or.inr ⟨i,hi,h⟩
  · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
    · exact ⟨i,Or.inl hi,h⟩
    · exact ⟨i,Or.inr hi,h⟩

private lemma restored_empty (E : ι → SimpleGraph V) : restored E ∅ = ⊥ := by
  ext x y
  simp [restored_adj_iff]

/-- Restoring the selected stages does not reconnect the endpoints of any residual cut edge. -/
def Preserves (L E : ι → SimpleGraph V) (S : Set ι) : Prop :=
  ∀ i ∉ S, ∀ ⦃x y⦄, (E i).Adj x y → ¬ (L i ⊔ restored E S).Reachable x y

private lemma support_restored_subset (E : ι → SimpleGraph V) (S : Set ι) :
    (restored E S).support ⊆ ⋃ i ∈ S, (E i).support := by
  intro x hx
  obtain ⟨y,hy⟩ := ((restored E S).mem_support).mp hx
  obtain ⟨i,hi,hij⟩ := (restored_adj_iff E S x y).mp hy
  exact mem_iUnion₂.mpr ⟨i,hi,hij.mem_support_left⟩

lemma countable_support_restored (E : ι → SimpleGraph V) {S : Set ι} (hS : S.Countable)
    (hE : ∀ i, (E i).support.Countable) : (restored E S).support.Countable :=
  (hS.biUnion (fun i _ => hE i)).mono (support_restored_subset E S)

private lemma reachable_in_monotone_union {J : Type*} [LinearOrder J] [Nonempty J]
    {G : J → SimpleGraph V} (hG : Monotone G) {x y : V}
    (h : (⨆ j, G j).Reachable x y) : ∃ j, (G j).Reachable x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ⟨j,Reachable.rfl⟩
  | cons h _ ih =>
    obtain ⟨j,hj⟩ := iSup_adj.mp h
    obtain ⟨k,hk⟩ := ih
    have hJ := (hG (le_max_left j k)) hj
    exact ⟨max j k,hJ.reachable.trans (Reachable.mono (hG (le_max_right j k)) hk)⟩

private lemma preserves_iUnion {J : Type*} [LinearOrder J] [Nonempty J]
    {S : J → Set ι} (hS : Monotone S) {L E : ι → SimpleGraph V}
    (hGood : ∀ j, Preserves L E (S j)) : Preserves L E (⋃ j, S j) := by
  intro i hi x y he hRe
  have hEq : L i ⊔ restored E (⋃ j, S j) = ⨆ j, (L i ⊔ restored E (S j)) := by
    ext u v
    simp only [sup_adj, restored_adj_iff, iSup_adj, mem_iUnion]
    constructor
    · rintro (hL | ⟨k,⟨j,hj⟩,hk⟩)
      · obtain ⟨j⟩ := ‹Nonempty J›
        exact ⟨j,Or.inl hL⟩
      · exact ⟨j,Or.inr ⟨k,hj,hk⟩⟩
    · rintro ⟨j,hL | ⟨k,hk,he⟩⟩
      · exact Or.inl hL
      · exact Or.inr ⟨k,⟨j,hk⟩,he⟩
  rw [hEq] at hRe
  have hm : Monotone (fun j => L i ⊔ restored E (S j)) :=
    fun j k hjk => sup_le_sup_left (restored_mono E (hS hjk)) _
  obtain ⟨j,hj⟩ := reachable_in_monotone_union hm hRe
  exact hGood j i (fun h => hi (mem_iUnion.mpr ⟨j,h⟩)) he hj

variable [LinearOrder ι]

private lemma exists_step {K L E : ι → SimpleGraph V}
    (hLe : ∀ i, L i ≤ K i) (hCut : ∀ i, E i ≤ K i)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i)
    (hE : ∀ i, (E i).support.Countable)
    {S : Set ι} (hGood : Preserves L E S) (hNe : S ≠ univ) :
    ∃ T : Set ι, S ⊂ T ∧ (T \ S).Countable ∧ Preserves L E T := by
  classical
  obtain ⟨k,hk⟩ : ∃ k, k ∉ S := by
    by_contra! h
    exact hNe (eq_univ_of_forall h)
  let K' (i : ι) := K i ⊔ restored E S
  let L' (i : ι) := L i ⊔ restored E S
  have hOrder' : ∀ ⦃i j⦄, i < j → K' j ≤ L' i := fun _ _ hi => sup_le_sup_right (hOrder hi) _
  obtain ⟨T,hkT,hT,hClosed⟩ := ThomassenCuts.countable_closed_extension K' L' hOrder'
    (fun i => (E i).support) hE (countable_singleton k)
  have hK : k ∈ T := hkT rfl
  refine ⟨S ∪ T,?_,hT.mono (fun i hi => hi.1.resolve_left hi.2),?_⟩
  · refine lt_of_le_of_ne subset_union_left ?_
    intro he
    have h : k ∈ S ∪ T := Or.inr hK
    rw [← he] at h
    exact hk h
  · intro i hi x y hei hNew
    have hiS : i ∉ S := fun hs => hi (Or.inl hs)
    have hiT : i ∉ T := fun ht => hi (Or.inr ht)
    apply hGood i hiS hei
    rw [restored_union, ← sup_assoc] at hNew
    have hLe' : L' i ≤ K' i := sup_le_sup_right (hLe i) _
    have hAdj : (K' i).Adj x y := (sup_adj _ _ _ _).mpr (Or.inl (hCut i hei))
    apply ThomassenCuts.reachable_of_preserved_endpoints hLe' _ hAdj.reachable hNew
    intro u hu v hv hr
    by_contra hnr
    exact hiT (hClosed ⟨u,support_restored_subset E T hu,v,support_restored_subset E T hv,hr,hnr⟩)

omit [LinearOrder ι] in
private lemma exists_entry_before (S : Ordinal.{w} → Set ι) (h0 : S 0 = ∅)
    (hLim : ∀ i, Order.IsSuccLimit i → S i = ⋃ j : Iio i, S j.val)
    (x : ι) (o : Ordinal.{w}) (hx : x ∈ S o) :
    ∃ j < o, x ∈ S (Order.succ j) \ S j := by
  induction o using SuccOrder.limitRecOn with
  | isMin i hi =>
    rw [hi.eq_bot, Ordinal.bot_eq_zero, h0] at hx
    exact hx.elim
  | succ i hi ih =>
    by_cases h : x ∈ S i
    · obtain ⟨j,hj,hx⟩ := ih h
      exact ⟨j,hj.trans (Order.lt_succ_of_not_isMax hi),hx⟩
    · exact ⟨i,Order.lt_succ_of_not_isMax hi,hx,h⟩
  | isSuccLimit i hi ih =>
    rw [hLim i hi] at hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    obtain ⟨k,hk,hkx⟩ := ih j.val j.property hj
    exact ⟨k,hk.trans j.property,hkx⟩

/-- Restore all cuts in a transfinite sequence whose successor blocks are countable. -/
theorem exists_chain {K L E : ι → SimpleGraph V}
    (hLe : ∀ i, L i ≤ K i) (hCut : ∀ i, E i ≤ K i)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i)
    (hE : ∀ i, (E i).support.Countable)
    (hSep : ∀ i ⦃x y⦄, (E i).Adj x y → ¬ (L i).Reachable x y) :
    ∃ (o : Ordinal.{w}) (S : Ordinal.{w} → Set ι),
      Monotone S ∧ (∀ j, Preserves L E (S j)) ∧
      (∀ j, (S (Order.succ j) \ S j).Countable) ∧
      ∀ i : ι, ∃ j < o, i ∈ S (Order.succ j) \ S j := by
  classical
  let φ (S : Set ι) : Set ι :=
    if h : Preserves L E S ∧ S ≠ univ then
      Classical.choose (exists_step hLe hCut hOrder hE h.1 h.2)
    else S
  have hProps (S : Set ι) (hS : Preserves L E S) (hNe : S ≠ univ) :
      S ⊂ φ S ∧ (φ S \ S).Countable ∧ Preserves L E (φ S) := by
    dsimp only [φ]
    rw [dif_pos ⟨hS,hNe⟩]
    exact Classical.choose_spec (exists_step hLe hCut hOrder hE hS hNe)
  have hInfl (S : Set ι) : S ≤ φ S := by
    by_cases h : Preserves L E S ∧ S ≠ univ
    · exact (hProps S h.1 h.2).1.1
    · simp only [φ,dif_neg h,le_refl]
  let S (j : Ordinal.{w}) := transfiniteIterate φ j (∅ : Set ι)
  have h0 : S 0 = ∅ := by simp only [S, ← Ordinal.bot_eq_zero, transfiniteIterate_bot]
  have hSucc (i : Ordinal.{w}) : S (Order.succ i) = φ (S i) :=
    transfiniteIterate_succ φ _ i (not_isMax i)
  have hLim (i : Ordinal.{w}) (hi : Order.IsSuccLimit i) : S i = ⋃ j : Iio i, S j.val :=
    transfiniteIterate_limit φ _ i hi
  have hMono : Monotone S := monotone_transfiniteIterate φ _ hInfl
  have hPres (i : Ordinal.{w}) : Preserves L E (S i) := by
    induction i using SuccOrder.limitRecOn with
    | isMin i hi =>
      rw [hi.eq_bot, Ordinal.bot_eq_zero, h0]
      intro j _ x y he
      simpa only [restored_empty, sup_bot_eq] using hSep j he
    | succ i hi ih =>
      rw [hSucc]
      by_cases hTop : S i = univ
      · have hNeg : ¬ (Preserves L E (S i) ∧ S i ≠ univ) := fun h => h.2 hTop
        simpa only [φ,dif_neg hNeg] using ih
      · exact (hProps _ ih hTop).2.2
    | isSuccLimit i hi ih =>
      rw [hLim i hi]
      have : Nonempty (Iio i) := ⟨⟨⊥,hi.bot_lt⟩⟩
      exact preserves_iUnion (S := fun j : Iio i => S j.val)
        (fun j k hjk => hMono hjk) (fun j => ih j.val j.property)
  have hCount (i : Ordinal.{w}) : (S (Order.succ i) \ S i).Countable := by
    rw [hSucc]
    by_cases hTop : S i = univ
    · rw [hTop, sdiff_univ]
      exact countable_empty
    · exact (hProps _ (hPres i) hTop).2.1
  have hFull : ∃ o, S o = univ := by
    by_contra! hn
    have hStrict : StrictMono S := by
      intro i j hij
      have hlt : S i < S (Order.succ i) := by
        rw [hSucc]
        exact (hProps _ (hPres i) (hn i)).1
      exact hlt.trans_le (hMono (Order.succ_le_of_lt hij))
    exact (not_injective_of_ordinal S) hStrict.injective
  obtain ⟨o,ho⟩ := hFull
  refine ⟨o,S,hMono,hPres,hCount,fun i => ?_⟩
  apply exists_entry_before S h0 hLim i o
  rw [ho]
  exact mem_univ i

omit [LinearOrder ι] in
/-- A cut still to be restored joins different components of the current graph. -/
theorem residual_separated {H : SimpleGraph V} {L E : ι → SimpleGraph V}
    (hH : ∀ i, H ≤ L i) {S : Set ι} (hGood : Preserves L E S)
    {i : ι} (hi : i ∉ S) {x y : V} (hxy : (E i).Adj x y) :
    ¬ (H ⊔ restored E S).Reachable x y :=
  fun h => hGood i hi hxy (Reachable.mono (sup_le_sup_right (hH i) _) h)

/-- Different residual stages cannot connect the same pair of current components. -/
theorem residual_same_stage {H : SimpleGraph V} {K L E : ι → SimpleGraph V}
    (hCut : ∀ i, E i ≤ K i) (hH : ∀ i, H ≤ L i)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i)
    {S : Set ι} (hGood : Preserves L E S) {i j : ι} (hi : i ∉ S) (hj : j ∉ S)
    {x y u v : V} (hxy : (E i).Adj x y) (huv : (E j).Adj u v)
    (h₁ : (H ⊔ restored E S).Reachable x u) (h₂ : (H ⊔ restored E S).Reachable y v) :
    i = j := by
  by_contra! hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : H ⊔ restored E S ≤ L i ⊔ restored E S := sup_le_sup_right (hH i) _
    have hNew : (L i ⊔ restored E S).Adj u v := (sup_adj _ _ _ _).mpr
      (Or.inl (hOrder hlt (hCut j huv)))
    exact hGood i hi hxy
      ((Reachable.mono hle h₁).trans (hNew.reachable.trans (Reachable.mono hle h₂).symm))
  · have hle : H ⊔ restored E S ≤ L j ⊔ restored E S := sup_le_sup_right (hH j) _
    have hNew : (L j ⊔ restored E S).Adj x y := (sup_adj _ _ _ _).mpr
      (Or.inl (hOrder hgt (hCut i hxy)))
    exact hGood j hj huv
      ((Reachable.mono hle h₁).symm.trans (hNew.reachable.trans (Reachable.mono hle h₂)))

end ThomassenRestore

namespace ThomassenOrientColor

open SimpleGraph Set Relation

variable {V : Type*}

/-- A countable set can be indexed injectively by natural numbers. -/
theorem countable_codes {S : Set V} (hS : S.Countable) : ∃ f : V → ℕ, InjOn f S := by
  classical
  have : Countable S := hS.to_subtype
  obtain ⟨f,hf⟩ := Countable.exists_injective_nat S
  refine ⟨fun v => if h : v ∈ S then f ⟨v,h⟩ else 0, ?_⟩
  intro x hx y hy he
  simp only [dif_pos hx, dif_pos hy] at he
  exact congrArg Subtype.val (hf he)

private lemma forward_countable (o : V → V → Prop)
    (hOut : ∀ v, {w | o v w}.Finite) (v : V) : {w | ReflTransGen o v w}.Countable := by
  let step (S : Set V) := S ∪ ⋃ x ∈ S, {y | o x y}
  let s : ℕ → Set V := Nat.rec {v} (fun _ S => step S)
  have hC (n : ℕ) : (s n).Countable := by
    induction n with
    | zero => exact countable_singleton v
    | succ n ih => exact ih.union (ih.biUnion fun x _ => (hOut x).countable)
  refine (countable_iUnion hC).mono ?_
  intro w hw
  induction hw with
  | refl => exact mem_iUnion.mpr ⟨0,rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n,hn⟩ := mem_iUnion.mp ih
    exact mem_iUnion.mpr ⟨n + 1,Or.inr (mem_iUnion₂.mpr ⟨b,hn,hbc⟩)⟩

private lemma color_from_predecessors {G : SimpleGraph V} {A : Type*}
    [LinearOrder A] [WellFoundedLT A] (tag : V → A) (hinj : Function.Injective tag)
    (hFinite : ∀ v, {w | G.Adj v w ∧ tag w < tag v}.Finite) :
    Nonempty (G.Coloring ℕ) := by
  let before (w v : V) := tag w < tag v
  have hW : WellFounded before := InvImage.wf tag wellFounded_lt
  have existsColor (v : V) (recColor : ∀ w, before w v → ℕ) :
      ∃ c, ∀ w (h : before w v), G.Adj v w → recColor w h ≠ c := by
    let neighbors : Set V := {w | G.Adj v w ∧ before w v}
    have : Finite neighbors := (hFinite v).to_subtype
    let f (w : neighbors) := recColor w.val w.property.2
    obtain ⟨c,hc⟩ := (finite_range f).exists_notMem
    exact ⟨c,fun w h ha he => hc ⟨⟨w,ha,h⟩,he⟩⟩
  let chooseColor (v : V) (recColor : ∀ w, before w v → ℕ) :=
    Classical.choose (existsColor v recColor)
  let color : V → ℕ := hW.fix chooseColor
  have good {v w : V} (h : before w v) (ha : G.Adj v w) : color w ≠ color v := by
    have he : color v = chooseColor v (fun x _ => color x) := hW.fix_eq chooseColor v
    rw [he]
    exact Classical.choose_spec (existsColor v (fun x _ => color x)) w h ha
  refine ⟨Coloring.mk color ?_⟩
  intro v w ha
  rcases lt_or_gt_of_ne (fun h => ha.ne (hinj h)) with h | h
  · exact good h ha.symm
  · exact (good h ha).symm

private lemma color_ordered [LinearOrder V] [WellFoundedLT V] (G : SimpleGraph V)
    (o : V → V → Prop) (hDir : ∀ ⦃x y⦄, G.Adj x y → o x y ∨ o y x)
    (hOut : ∀ v, {w | o v w}.Finite) : Nonempty (G.Coloring ℕ) := by
  classical
  let pred (v : V) : Set V := {w | ReflTransGen o w v}
  have hPred (v : V) : (pred v).Nonempty := ⟨v,ReflTransGen.refl⟩
  let owner (v : V) := wellFounded_lt.min (pred v) (hPred v)
  have hOwn (v : V) : ReflTransGen o (owner v) v := wellFounded_lt.min_mem (pred v) (hPred v)
  have hMin {u v : V} (h : ReflTransGen o u v) : owner v ≤ u :=
    le_of_not_gt (wellFounded_lt.not_lt_min (pred v) (x := u) h)
  have hDirOwner {v w : V} (h : o v w) : owner w ≤ owner v := hMin ((hOwn v).tail h)
  let fiber (u : V) : Set V := {v | owner v = u}
  have hFiber (u : V) : (fiber u).Countable := by
    apply (forward_countable o hOut u).mono
    intro v hv
    exact hv ▸ hOwn v
  have hCodes (u : V) : ∃ f : V → ℕ, InjOn f (fiber u) := countable_codes (hFiber u)
  choose codeFor hCodeFor using hCodes
  let code (v : V) := codeFor (owner v) v
  have hCode {v w : V} (h : owner v = owner w) (hc : code v = code w) : v = w :=
    hCodeFor (owner w) h rfl (by simpa only [code,h] using hc)
  let tag (v : V) : V ×ₗ ℕ := toLex (owner v,code v)
  have hInj : Function.Injective tag := by
    intro v w h
    have he : (owner v,code v) = (owner w,code w) := congrArg ofLex h
    exact hCode (congrArg Prod.fst he) (congrArg Prod.snd he)
  apply color_from_predecessors tag hInj
  intro v
  have hEarly : {w | owner w = owner v ∧ code w < code v}.Finite := by
    apply (finite_Iio (code v)).of_injOn (f := code)
    · intro w hw
      exact hw.2
    · intro x hx y hy he
      exact hCode (hx.1.trans hy.1.symm) he
  apply ((hOut v).union hEarly).subset
  intro w hw
  rcases hDir hw.1 with ho | ho
  · exact Or.inl ho
  · obtain ⟨hle,hc⟩ := Prod.Lex.toLex_lt_toLex'.mp hw.2
    have he := hle.antisymm (hDirOwner ho)
    exact Or.inr ⟨he,hc he⟩

/-- A graph with a finite-outdegree orientation has a countable proper vertex coloring. -/
theorem countable_coloring (G : SimpleGraph V) (o : V → V → Prop)
    (hDir : ∀ ⦃x y⦄, G.Adj x y → o x y ∨ o y x)
    (hOut : ∀ v, {w | o v w}.Finite) : Nonempty (G.Coloring ℕ) := by
  obtain ⟨ord,hWell⟩ := exists_wellFoundedLT V
  exact @color_ordered V ord hWell G o hDir hOut

end ThomassenOrientColor

namespace ThomassenBlocks

open SimpleGraph Set ThomassenRestore

variable {V ι : Type*}

private lemma finite_star {G : SimpleGraph V} (hG : G.edgeSet.Finite) (x : V) :
    {y | G.Adj x y}.Finite := by
  apply hG.of_injOn (f := fun y => s(x,y))
  · intro y hy
    exact G.mem_edgeSet.mpr hy
  · intro y _ z _ h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1

private lemma finite_support {G : SimpleGraph V} (hG : G.edgeSet.Finite) :
    G.support.Finite := by
  classical
  have hf : (⋃ e ∈ G.edgeSet, (e.toFinset : Set V)).Finite :=
    hG.biUnion (fun e _ => e.toFinset.finite_toSet)
  apply hf.subset
  intro x hx
  obtain ⟨y,hy⟩ := G.mem_support.mp hx
  exact mem_iUnion₂.mpr ⟨s(x,y),G.mem_edgeSet.mpr hy,Sym2.mem_toFinset.mpr (by simp)⟩

section Ordered

variable [LinearOrder V] [WellFoundedLT V]

private noncomputable def root (G : SimpleGraph V) (x : V) : V :=
  wellFounded_lt.min {y | G.Reachable x y} ⟨x,Reachable.rfl⟩

private lemma root_reach (G : SimpleGraph V) (x : V) : G.Reachable x (root G x) :=
  wellFounded_lt.min_mem {y | G.Reachable x y} ⟨x,Reachable.rfl⟩

private lemma root_le {G : SimpleGraph V} {x y : V} (h : G.Reachable x y) : root G x ≤ y :=
  le_of_not_gt (wellFounded_lt.not_lt_min {v | G.Reachable x v} (x := y) h)

private lemma root_eq {G : SimpleGraph V} {x y : V} (h : G.Reachable x y) :
    root G x = root G y :=
  le_antisymm (root_le (h.trans (root_reach G y))) (root_le (h.symm.trans (root_reach G x)))

private lemma reachable_of_root_eq {G : SimpleGraph V} {x y : V} (h : root G x = root G y) :
    G.Reachable x y :=
  (root_reach G x).trans (h.symm ▸ (root_reach G y).symm)

private lemma root_of_le {G H : SimpleGraph V} (h : G ≤ H) (v : V) :
    root H v ≤ root G v :=
  root_le (Reachable.mono h (root_reach G v))

private theorem orientation_block (A B D : SimpleGraph V)
    (hA : A ≤ B) (hD : D ≤ B) (hSupp : D.support.Countable)
    (hSep : ∀ ⦃x y⦄, D.Adj x y → ¬ A.Reachable x y)
    (hFin : ∀ x t, {y | D.Adj x y ∧ A.Reachable t y}.Finite) :
    ∃ o : V → V → Prop,
      (∀ ⦃x y⦄, D.Adj x y → o x y ∨ o y x) ∧
      (∀ x, {y | o x y}.Finite) ∧ (∀ ⦃x y⦄, o x y → root B x < root A x) := by
  classical
  let touched := root A '' D.support
  have ht : touched.Countable := hSupp.image (root A)
  obtain ⟨code,hCode⟩ := ThomassenOrientColor.countable_codes ht
  let score (v : V) : ℕ := if root A v = root B v then 0 else code (root A v) + 1
  have hScore {x y : V} (hx : x ∈ D.support) (hy : y ∈ D.support)
      (hB : root B x = root B y) (hs : score x = score y) : root A x = root A y := by
    by_cases hx' : root A x = root B x <;> by_cases hy' : root A y = root B y
    · exact hx'.trans (hB.trans hy'.symm)
    · simp [score,hx',hy'] at hs
    · simp [score,hx',hy'] at hs
    · have he : code (root A x) = code (root A y) := by simpa [score,hx',hy'] using hs
      exact hCode ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩ he
  let o (x y : V) := D.Adj x y ∧ score y < score x
  refine ⟨o,?_,?_,?_⟩
  · intro x y hxy
    have hB := root_eq (hD hxy).reachable
    have hne : score x ≠ score y := fun h =>
      hSep hxy (reachable_of_root_eq (hScore hxy.mem_support_left hxy.mem_support_right hB h))
    rcases lt_or_gt_of_ne hne with hn | hn
    · exact Or.inr ⟨hxy.symm,hn⟩
    · exact Or.inl ⟨hxy,hn⟩
  · intro x
    let early : Set V := {w | ∃ v, o x v ∧ root A v = w}
    let scoreRoot (w : V) := if w = root B x then 0 else code w + 1
    have score_eq {v : V} (hv : o x v) : scoreRoot (root A v) = score v := by
      have h := root_eq (hD hv.1).reachable
      simp only [scoreRoot,score,h]
    have hEarly : early.Finite := by
      apply (finite_Iio (score x)).of_injOn (f := scoreRoot)
      · rintro w ⟨v,hv,rfl⟩
        change scoreRoot (root A v) < score x
        rw [score_eq hv]
        exact hv.2
      · rintro u ⟨v,hv,rfl⟩ w ⟨t,ht,rfl⟩ h
        rw [score_eq hv,score_eq ht] at h
        have hB := (root_eq (hD hv.1).reachable).symm.trans (root_eq (hD ht.1).reachable)
        exact hScore hv.1.mem_support_right ht.1.mem_support_right hB h
    apply (hEarly.biUnion (fun w _ => hFin x w)).subset
    intro v hv
    exact mem_iUnion₂.mpr ⟨root A v,⟨v,hv,rfl⟩,hv.1,(root_reach A v).symm⟩
  · intro x y hxy
    refine lt_of_le_of_ne (root_of_le hA x) ?_
    intro h
    have hzero : score x = 0 := if_pos h.symm
    have hlt := hxy.2
    rw [hzero] at hlt
    omega

universe w

private theorem orientation_restoration {ι : Type w} [LinearOrder ι] (H : SimpleGraph V)
    {K L E : ι → SimpleGraph V}
    (hLe : ∀ i, L i ≤ K i) (hCut : ∀ i, E i ≤ K i)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i) (hH : ∀ i, H ≤ L i)
    (hE : ∀ i, (E i).edgeSet.Finite)
    (hSep : ∀ i ⦃x y⦄, (E i).Adj x y → ¬ (L i).Reachable x y) :
    ∃ o : V → V → Prop,
      (∀ ⦃x y⦄, (⨆ i, E i).Adj x y → o x y ∨ o y x) ∧ (∀ x, {y | o x y}.Finite) := by
  classical
  have hSupp (i : ι) : (E i).support.Countable := (finite_support (hE i)).countable
  obtain ⟨a,S,hMono,hPres,hCount,hCover⟩ := exists_chain hLe hCut hOrder hSupp hSep
  let A (j : Ordinal.{w}) := H ⊔ restored E (S j)
  let block (j : Ordinal.{w}) := S (Order.succ j) \ S j
  let D (j : Ordinal.{w}) := restored E (block j)
  have hAm : Monotone A :=
    fun _ _ h => sup_le_sup_left (restored_mono E (hMono h)) _
  have hDA (j : Ordinal.{w}) : D j ≤ A (Order.succ j) :=
    (restored_mono E sdiff_subset).trans le_sup_right
  have hDsep (j : Ordinal.{w}) {x y : V} (hxy : (D j).Adj x y) : ¬ (A j).Reachable x y := by
    obtain ⟨i,hi,hxy⟩ := (restored_adj_iff E (block j) x y).mp hxy
    exact residual_separated hH (hPres j) hi.2 hxy
  have hPair (j : Ordinal.{w}) (x t : V) : {y | (D j).Adj x y ∧ (A j).Reachable t y}.Finite := by
    let Q : Set V := {y | (D j).Adj x y ∧ (A j).Reachable t y}
    rcases Q.eq_empty_or_nonempty with he | ⟨u,hu⟩
    · rw [← show Q = {y | (D j).Adj x y ∧ (A j).Reachable t y} from rfl,he]
      exact finite_empty
    · obtain ⟨i,hi,hxu⟩ := (restored_adj_iff E (block j) x u).mp hu.1
      apply (finite_star (hE i) x).subset
      intro v hv
      obtain ⟨k,hk,hxv⟩ := (restored_adj_iff E (block j) x v).mp hv.1
      have hie := residual_same_stage hCut hH hOrder (hPres j) hi.2 hk.2 hxu hxv
        Reachable.rfl (hu.2.symm.trans hv.2)
      exact hie.symm ▸ hxv
  have hOr (j : Ordinal.{w}) : ∃ o : V → V → Prop,
      (∀ ⦃x y⦄, (D j).Adj x y → o x y ∨ o y x) ∧ (∀ x, {y | o x y}.Finite) ∧
        (∀ ⦃x y⦄, o x y → root (A (Order.succ j)) x < root (A j) x) :=
    orientation_block _ _ _ (hAm (Order.le_succ _)) (hDA j)
      (countable_support_restored E (hCount j) hSupp) (fun _ _ h => hDsep j h) (hPair j)
  choose o ho hFin hDrop using hOr
  let orient (x y : V) := ∃ j : Ordinal.{w}, o j x y
  refine ⟨orient,?_,?_⟩
  · intro x y hxy
    obtain ⟨i,hi⟩ := iSup_adj.mp hxy
    obtain ⟨j,_,hj⟩ := hCover i
    exact (ho j ((restored_adj_iff E (block j) x y).mpr ⟨i,hj,hi⟩)).imp
      (fun h => ⟨j,h⟩) (fun h => ⟨j,h⟩)
  · intro x
    let relevant : Set Ordinal.{w} := {j | ∃ y, o j x y}
    have hRel : relevant.Finite := by
      by_contra hnf
      have : Infinite relevant := Set.infinite_coe_iff.mpr hnf
      obtain ⟨f,hf | hf⟩ := Infinite.exists_strictMono_or_strictAnti relevant
      · have hAnti : StrictAnti (fun n => root (A (f n).val) x) := by
          intro n m hnm
          have hm : (f n).val < (f m).val := hf hnm
          obtain ⟨y,hy⟩ := (f n).property
          exact (root_of_le (hAm (Order.succ_le_of_lt hm)) x).trans_lt (hDrop (f n).val hy)
        exact not_strictAnti_of_wellFoundedLT _ hAnti
      · exact not_strictAnti_of_wellFoundedLT f hf
    apply (hRel.biUnion (fun j _ => hFin j x)).subset
    intro y hy
    obtain ⟨j,hj⟩ := hy
    exact mem_iUnion₂.mpr ⟨j,⟨y,hj⟩,hj⟩

end Ordered

/-- The deleted edges of a finite-cut descent have a countable proper coloring. -/
theorem countable_deleted [LinearOrder ι] (H : SimpleGraph V)
    {K L E : ι → SimpleGraph V}
    (hLe : ∀ i, L i ≤ K i) (hCut : ∀ i, E i ≤ K i)
    (hOrder : ∀ ⦃i j⦄, i < j → K j ≤ L i) (hH : ∀ i, H ≤ L i)
    (hE : ∀ i, (E i).edgeSet.Finite)
    (hSep : ∀ i ⦃x y⦄, (E i).Adj x y → ¬ (L i).Reachable x y) :
    Nonempty ((⨆ i, E i).Coloring ℕ) := by
  obtain ⟨ord,hWell⟩ := exists_wellFoundedLT V
  obtain ⟨o,hDir,hOut⟩ := @orientation_restoration V ord hWell ι _ H K L E hLe hCut hOrder hH hE hSep
  exact ThomassenOrientColor.countable_coloring _ o hDir hOut

theorem countable_coloring_sup {G H : SimpleGraph V} (hG : Nonempty (G.Coloring ℕ))
    (hH : Nonempty (H.Coloring ℕ)) : Nonempty ((G ⊔ H).Coloring ℕ) := by
  obtain ⟨g⟩ := hG
  obtain ⟨h⟩ := hH
  refine ⟨Coloring.mk (fun v => Encodable.encode (g v,h v)) ?_⟩
  intro x y hxy he
  have hEq := Encodable.encode_injective he
  rcases (sup_adj G H x y).mp hxy with hg | hh
  · exact g.valid hg (congrArg Prod.fst hEq)
  · exact h.valid hh (congrArg Prod.snd hEq)

end ThomassenBlocks

/- Chromatic cardinal and finite-edge deletion in terminal connected components. -/

open Cardinal Set SimpleGraph
open scoped Cardinal

namespace ThomassenComponents

universe u
variable {V W : Type u}

private theorem color_at_cardinal (G : SimpleGraph V) :
    ∃ C : Type u, Cardinal.mk C = G.chromaticCardinal ∧ Nonempty (G.Coloring C) := by
  let S : Set Cardinal.{u} := {κ | ∃ (C : Type u) (_ : Cardinal.mk C = κ),
    Nonempty (G.Coloring C)}
  have hS : S.Nonempty := ⟨Cardinal.mk V, V, rfl, ⟨G.selfColoring⟩⟩
  obtain ⟨C, hC, hc⟩ := csInf_mem hS
  exact ⟨C, hC, hc⟩

private theorem cardinal_le_of_coloring {G : SimpleGraph V} {C : Type u}
    (f : G.Coloring C) : G.chromaticCardinal ≤ Cardinal.mk C := by
  unfold SimpleGraph.chromaticCardinal
  exact csInf_le (OrderBot.bddBelow _) ⟨C, rfl, ⟨f⟩⟩

private theorem cardinal_le_of_hom {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : G.chromaticCardinal ≤ H.chromaticCardinal := by
  obtain ⟨C, hC, ⟨c⟩⟩ := color_at_cardinal H
  rw [← hC]
  exact cardinal_le_of_coloring (c.comp f)

theorem countably_colorable {G : SimpleGraph V} :
    G.chromaticCardinal ≤ ℵ₀ ↔ Nonempty (G.Coloring ℕ) := by
  have hNat : Cardinal.mk (ULift.{u} ℕ) = ℵ₀ := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
  constructor
  · intro h
    obtain ⟨C, hC, ⟨c⟩⟩ := color_at_cardinal G
    have hle : Cardinal.mk C ≤ Cardinal.mk (ULift.{u} ℕ) := by rw [hC, hNat]; exact h
    obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hle
    exact ⟨SimpleGraph.Coloring.mk (fun v => (e (c v)).down)
      (fun hadj heq => c.valid hadj (e.injective (ULift.ext _ _ heq)))⟩
  · rintro ⟨c⟩
    rw [← hNat]
    exact cardinal_le_of_coloring (SimpleGraph.Coloring.mk (fun v => ULift.up (c v))
      (fun hadj heq => c.valid hadj (congrArg ULift.down heq)))

private theorem reachable_after_delete {H : SimpleGraph V} {S : Set (Sym2 V)}
    (h : ∀ ⦃x y⦄, H.Adj x y → (H.deleteEdges S).Reachable x y)
    {u v : V} (p : H.Walk u v) : (H.deleteEdges S).Reachable u v := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h hadj).trans ih

private theorem reachable_in_component {H : SimpleGraph V} (C : H.ConnectedComponent)
    (S : Set (Sym2 C)) {u v : V}
    (p : (H.deleteEdges ((Sym2.map Subtype.val) '' S)).Walk u v)
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) :
    (C.toSimpleGraph.deleteEdges S).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w v hadj _ ih =>
      obtain ⟨huw, havoids⟩ := SimpleGraph.deleteEdges_adj.mp hadj
      have hw := C.mem_supp_of_adj_mem_supp hu huw
      have hsub : (C.toSimpleGraph.deleteEdges S).Adj ⟨u, hu⟩ ⟨w, hw⟩ := by
        refine SimpleGraph.deleteEdges_adj.mpr ⟨huw, fun h => havoids ?_⟩
        exact ⟨s(⟨u, hu⟩, ⟨w, hw⟩), h, rfl⟩
      exact hsub.reachable.trans (ih hw hv)

private theorem robust_component {H : SimpleGraph V}
    (h : ∀ ⦃x y⦄, H.Adj x y →
      ∀ S : Set (Sym2 V), S.Finite → (H.deleteEdges S).Reachable x y)
    (C : H.ConnectedComponent) : Erdos1067.InfinitelyEdgeConnected C.toSimpleGraph := by
  intro S hS
  refine { preconnected := ?_, nonempty := C.connected_toSimpleGraph.nonempty }
  intro u v
  have hp := C.reachable_of_mem_supp u.property v.property
  have hq := reachable_after_delete (S := (Sym2.map Subtype.val) '' S)
    (fun _ _ hxy => h hxy _ (hS.image _)) hp.some
  exact reachable_in_component C S hq.some u.property v.property

private theorem exists_uncountable_component {H : SimpleGraph V}
    (hc : ℵ₀ < H.chromaticCardinal) :
    ∃ C : H.ConnectedComponent, ℵ₀ < C.toSimpleGraph.chromaticCardinal := by
  by_contra! hall
  apply (not_le_of_gt hc)
  apply countably_colorable.mpr
  exact ⟨H.homOfConnectedComponents (fun C => (countably_colorable.mp (hall C)).some)⟩

theorem exists_robust_subgraph {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : G.chromaticCardinal = ℵ₁) (hH : ℵ₀ < H.chromaticCardinal)
    (h : ∀ ⦃x y⦄, H.Adj x y →
      ∀ S : Set (Sym2 V), S.Finite → (H.deleteEdges S).Reachable x y) :
    ∃ K : G.Subgraph, K.coe.chromaticCardinal = ℵ₁ ∧
      Erdos1067.InfinitelyEdgeConnected K.coe := by
  obtain ⟨C, hc⟩ := exists_uncountable_component hH
  let K := (SimpleGraph.toSubgraph H hHG).induce C.supp
  have hK : K.coe = C.toSimpleGraph := by
    ext x y
    exact ⟨fun hxy => hxy.2.2, fun hxy => ⟨x.property, y.property, hxy⟩⟩
  have hUpper : C.toSimpleGraph.chromaticCardinal ≤ ℵ₁ :=
    hG ▸ cardinal_le_of_hom ((SimpleGraph.Hom.ofLE hHG).comp C.toSimpleGraph_hom)
  have hLower : ℵ₁ ≤ C.toSimpleGraph.chromaticCardinal :=
    Cardinal.aleph_one_le_iff.mpr hc
  exact ⟨K, hK ▸ le_antisymm hUpper hLower, hK ▸ robust_component h C⟩

end ThomassenComponents

open scoped Cardinal

theorem OMA.solution : type_of% @Erdos1067.erdos_1067.variants.infinite_edge_connectivity := by
  intro V G hG
  obtain ⟨_, H, K, L, E, hHG, hRobust, hStage, hOrder, hH, hPartition⟩ :=
    ThomassenDescent.exists_sequence G
  have hLe (i : _) : L i ≤ K i := by rw [(hStage i).2.2.1]; exact sdiff_le
  have hDeleted := ThomassenBlocks.countable_deleted H hLe
    (fun i => (hStage i).1) hOrder hH (fun i => (hStage i).2.1)
    (fun i => (hStage i).2.2.2)
  have hUncountable : Cardinal.aleph0 < H.chromaticCardinal := by
    by_contra! hCount
    have hCol := ThomassenBlocks.countable_coloring_sup
      (ThomassenComponents.countably_colorable.mp hCount) hDeleted
    have hColG : Nonempty (G.Coloring ℕ) := hPartition.symm ▸ hCol
    have hSmall := ThomassenComponents.countably_colorable.mpr hColG
    rw [hG] at hSmall
    exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hSmall
  exact ThomassenComponents.exists_robust_subgraph hHG hG hUncountable hRobust