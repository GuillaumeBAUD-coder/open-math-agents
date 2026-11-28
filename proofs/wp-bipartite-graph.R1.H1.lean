import OMAReductions.R_wp_bipartite_graph_R1
import Mathlib

namespace OMA.Proof_wp_bipartite_graph_R1_H1

open OMA.S_wp_bipartite_graph

/-! ### Part 1: General helper lemmas on `Alternate` and `IsRepresentedBy` -/

private lemma isChain_ne_map_iff {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (l : List α) : List.IsChain (· ≠ ·) (l.map f) ↔ List.IsChain (· ≠ ·) l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y rest =>
      simp only [List.map_cons, List.isChain_cons_cons, hf.ne_iff]
      exact and_congr_right fun _ => ih

private lemma isRepresentedBy_transport {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hadj : ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v))
    {k : ℕ} {w : List W} (hw : IsRepresentedBy H k w) :
    IsRepresentedBy G k (w.map e.symm) := by
  constructor
  · intro v
    have hcount : (w.map e.symm).count v = w.count (e v) := by
      have h1 := List.count_map_of_injective w e.symm e.symm.injective (e v)
      simpa using h1
    rw [hcount, hw.1 (e v)]
  · intro a b hab
    rw [hadj a b, hw.2 (e a) (e b) (e.injective.ne hab)]
    unfold Alternate
    have hfilt : (w.map e.symm).filter (fun x => decide (x = a ∨ x = b)) =
        (w.filter (fun y => decide (y = e a ∨ y = e b))).map e.symm := by
      rw [List.filter_map]
      congr 1
      congr 1
      funext y
      simp only [Function.comp_apply, decide_eq_decide]
      constructor
      · rintro (h | h)
        · left; exact e.symm_apply_eq.mp h
        · right; exact e.symm_apply_eq.mp h
      · rintro (rfl | rfl) <;> simp
    rw [hfilt]
    exact (isChain_ne_map_iff e.symm e.symm.injective _).symm

private lemma filter_or_not_mem {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (ha : a ∉ L) (hb : b ∉ L) :
    L.filter (fun x => decide (x = a ∨ x = b)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [decide_eq_true_eq, not_or]
  exact ⟨fun h => ha (h ▸ hx), fun h => hb (h ▸ hx)⟩

private lemma filter_or_left_mem {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∉ L) :
    L.filter (fun x => decide (x = a ∨ x = b)) = [a] := by
  induction L with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons, not_or] at ha hb
    rcases ha with rfl | hax
    · simp only [List.filter_cons, true_or, decide_true, ↓reduceIte]
      rw [filter_or_not_mem hnd.1 hb.2]
    · have hxa : x ≠ a := fun h => hnd.1 (h ▸ hax)
      have hxb : x ≠ b := Ne.symm hb.1
      simp only [List.filter_cons, hxa, hxb, or_self, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih hnd.2 hax hb.2

private lemma filter_or_right_mem {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (hnd : L.Nodup) (ha : a ∉ L) (hb : b ∈ L) :
    L.filter (fun x => decide (x = a ∨ x = b)) = [b] := by
  have hcomm : (fun x : α => decide (x = a ∨ x = b)) = (fun x => decide (x = b ∨ x = a)) := by
    funext x; simp [or_comm]
  rw [hcomm]
  exact filter_or_left_mem hnd hb ha

private lemma filter_or_both_mem {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    L.filter (fun x => decide (x = a ∨ x = b)) = [a, b] ∨
    L.filter (fun x => decide (x = a ∨ x = b)) = [b, a] := by
  induction L with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | hax
    · rcases hb with hba | hbx
      · exact absurd hba.symm hab
      · left
        simp only [List.filter_cons, true_or, decide_true, ↓reduceIte]
        rw [filter_or_right_mem hnd.2 hnd.1 hbx]
    · rcases hb with rfl | hbx
      · right
        simp only [List.filter_cons, or_true, decide_true, ↓reduceIte]
        rw [filter_or_left_mem hnd.2 hax hnd.1]
      · have hxa : x ≠ a := fun h => hnd.1 (h ▸ hax)
        have hxb : x ≠ b := fun h => hnd.1 (h ▸ hbx)
        simp only [List.filter_cons, hxa, hxb, or_self, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih hnd.2 hax hbx

private lemma filter_flatMap_pair_not_mem {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (ha : a ∉ L) (hb : b ∉ L) :
    (L.flatMap (fun x => [x, x])).filter (fun x => decide (x = a ∨ x = b)) = [] := by
  apply filter_or_not_mem
  · simp [List.mem_flatMap, ha]
  · simp [List.mem_flatMap, hb]

private lemma filter_flatMap_pair_left {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∉ L) :
    (L.flatMap (fun x => [x, x])).filter (fun x => decide (x = a ∨ x = b)) = [a, a] := by
  induction L with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons, not_or] at ha hb
    rcases ha with rfl | hax
    · simp only [List.flatMap_cons, List.filter_append, List.filter_cons, true_or, decide_true,
        ↓reduceIte, List.filter_nil]
      rw [filter_flatMap_pair_not_mem hnd.1 hb.2, List.append_nil]
    · have hxa : x ≠ a := fun h => hnd.1 (h ▸ hax)
      have hxb : x ≠ b := Ne.symm hb.1
      simp only [List.flatMap_cons, List.filter_append, List.filter_cons, hxa, hxb, or_self,
        decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.nil_append]
      exact ih hnd.2 hax hb.2

private lemma filter_flatMap_pair_right {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (hnd : L.Nodup) (ha : a ∉ L) (hb : b ∈ L) :
    (L.flatMap (fun x => [x, x])).filter (fun x => decide (x = a ∨ x = b)) = [b, b] := by
  have hcomm : (fun x : α => decide (x = a ∨ x = b)) = (fun x => decide (x = b ∨ x = a)) := by
    funext x; simp [or_comm]
  rw [hcomm]
  exact filter_flatMap_pair_left hnd hb ha

private lemma filter_flatMap_pair_both {α : Type*} [DecidableEq α] {L : List α} {a b : α}
    (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    (L.flatMap (fun x => [x, x])).filter (fun x => decide (x = a ∨ x = b)) = [a, a, b, b] ∨
    (L.flatMap (fun x => [x, x])).filter (fun x => decide (x = a ∨ x = b)) = [b, b, a, a] := by
  induction L with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | hax
    · rcases hb with hba | hbx
      · exact absurd hba.symm hab
      · left
        simp only [List.flatMap_cons, List.filter_append, List.filter_cons, true_or, decide_true,
          ↓reduceIte, List.filter_nil]
        rw [filter_flatMap_pair_right hnd.2 hnd.1 hbx]
        rfl
    · rcases hb with rfl | hbx
      · right
        simp only [List.flatMap_cons, List.filter_append, List.filter_cons, or_true, decide_true,
          ↓reduceIte, List.filter_nil]
        rw [filter_flatMap_pair_left hnd.2 hax hnd.1]
        rfl
      · have hxa : x ≠ a := fun h => hnd.1 (h ▸ hax)
        have hxb : x ≠ b := fun h => hnd.1 (h ▸ hbx)
        simp only [List.flatMap_cons, List.filter_append, List.filter_cons, hxa, hxb, or_self,
          decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.nil_append]
        exact ih hnd.2 hax hbx

private lemma count_flatMap_pair {α : Type*} [DecidableEq α] (L : List α) (v : α) :
    (L.flatMap (fun x => [x, x])).count v = 2 * L.count v := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.count_append, List.count_cons, List.count_nil, ih]
    by_cases h : x = v
    · simp [h]; omega
    · simp [h]

private lemma not_isChain_aa_bb {α : Type*} (a b : α) :
    ¬ List.IsChain (· ≠ ·) [a, a, b, b] := by
  simp

/-! ### Part 2: Explicit 2-uniform construction when one bipartition class has size `≤ 2` -/

private lemma bipartite_le_two {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (hA_ind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hB_ind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hA_le : A.card ≤ 2) :
    ∃ w : List V, IsRepresentedBy G 2 w := by
  have hmem : ∀ v : V, v ∈ A ∨ v ∈ B := fun v => by
    have : v ∈ A ∪ B := hcover ▸ Finset.mem_univ v
    exact Finset.mem_union.mp this
  have hnotB : ∀ v ∈ A, v ∉ B := fun v hv => Finset.disjoint_left.mp hdisj hv
  have hA012 : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 := by omega
  rcases hA012 with hA0 | hA1 | hA2
  · -- Case |A| = 0
    have hAempty : A = ∅ := Finset.card_eq_zero.mp hA0
    let LB := B.toList
    have hLB_nd : LB.Nodup := Finset.nodup_toList B
    refine ⟨LB.flatMap (fun x => [x, x]), ?_, ?_⟩
    · intro v
      have hvB : v ∈ B := (hmem v).resolve_left (by simp [hAempty])
      rw [count_flatMap_pair, List.Nodup.count hLB_nd]
      simp [LB, hvB]
    · intro u v huv
      have huB : u ∈ B := (hmem u).resolve_left (by simp [hAempty])
      have hvB : v ∈ B := (hmem v).resolve_left (by simp [hAempty])
      have hno : ¬ G.Adj u v := hB_ind u huB v hvB
      simp only [hno, false_iff, Alternate]
      rcases filter_flatMap_pair_both hLB_nd (Finset.mem_toList.mpr huB)
          (Finset.mem_toList.mpr hvB) huv with h | h <;> rw [h]
      · exact not_isChain_aa_bb u v
      · exact not_isChain_aa_bb v u
  · -- Case |A| = 1
    obtain ⟨a₁, rfl⟩ := Finset.card_eq_one.mp hA1
    have ha₁_notB : a₁ ∉ B := hnotB a₁ (Finset.mem_singleton_self a₁)
    let B₁ := (B.filter (fun b => G.Adj a₁ b)).toList
    let B₀ := (B.filter (fun b => ¬ G.Adj a₁ b)).toList
    have hB₁_nd : B₁.Nodup := Finset.nodup_toList _
    have hB₀_nd : B₀.Nodup := Finset.nodup_toList _
    have hB₁_mem : ∀ x, x ∈ B₁ ↔ x ∈ B ∧ G.Adj a₁ x := by intro x; simp [B₁]
    have hB₀_mem : ∀ x, x ∈ B₀ ↔ x ∈ B ∧ ¬ G.Adj a₁ x := by intro x; simp [B₀]
    let w : List V := [a₁] ++ B₁ ++ [a₁] ++ B₁.reverse ++ B₀.flatMap (fun x => [x, x])
    refine ⟨w, ?_, ?_⟩
    · intro v
      simp only [w, List.count_append, List.count_reverse, count_flatMap_pair,
        List.Nodup.count hB₁_nd, List.Nodup.count hB₀_nd, List.count_singleton]
      by_cases hva : v = a₁
      · subst v
        have h1 : a₁ ∉ B₁ := fun h => ha₁_notB ((hB₁_mem a₁).mp h).1
        have h0 : a₁ ∉ B₀ := fun h => ha₁_notB ((hB₀_mem a₁).mp h).1
        simp [h1, h0]
      · have hvB : v ∈ B := (hmem v).resolve_left (by simp [hva])
        by_cases hadj : G.Adj a₁ v
        · have h1 : v ∈ B₁ := (hB₁_mem v).mpr ⟨hvB, hadj⟩
          have h0 : v ∉ B₀ := fun h => ((hB₀_mem v).mp h).2 hadj
          simp [Ne.symm hva, h1, h0]
        · have h1 : v ∉ B₁ := fun h => hadj ((hB₁_mem v).mp h).2
          have h0 : v ∈ B₀ := (hB₀_mem v).mpr ⟨hvB, hadj⟩
          simp [Ne.symm hva, h1, h0]
    · intro u v huv
      have hsym : ∀ x y : V, x ≠ y → (G.Adj x y ↔ Alternate w x y) → (G.Adj y x ↔ Alternate w y x) := by
        intro x y _ hxy
        have hf : (fun z : V => decide (z = y ∨ z = x)) = (fun z => decide (z = x ∨ z = y)) := by
          funext z; simp [or_comm]
        rw [SimpleGraph.adj_comm, hxy]
        unfold Alternate
        rw [hf]
      have ha₁_not1 : a₁ ∉ B₁ := fun h => ha₁_notB ((hB₁_mem a₁).mp h).1
      have ha₁_not0 : a₁ ∉ B₀ := fun h => ha₁_notB ((hB₀_mem a₁).mp h).1
      have hfw (x y : V) :
          w.filter (fun z => decide (z = x ∨ z = y)) =
            ([a₁].filter (fun z => decide (z = x ∨ z = y))) ++
            (B₁.filter (fun z => decide (z = x ∨ z = y))) ++
            ([a₁].filter (fun z => decide (z = x ∨ z = y))) ++
            (B₁.filter (fun z => decide (z = x ∨ z = y))).reverse ++
            ((B₀.flatMap (fun t => [t, t])).filter (fun z => decide (z = x ∨ z = y))) := by
        simp only [w, List.filter_append, List.filter_reverse]
      have h_a1_b : ∀ b ∈ B, G.Adj a₁ b ↔ Alternate w a₁ b := by
        intro b hb
        have hba : a₁ ≠ b := fun h => ha₁_notB (h ▸ hb)
        by_cases hadj : G.Adj a₁ b
        · have hv1 : b ∈ B₁ := (hB₁_mem b).mpr ⟨hb, hadj⟩
          have hv0 : b ∉ B₀ := fun h => ((hB₀_mem b).mp h).2 hadj
          simp only [hadj, true_iff, Alternate, hfw]
          rw [filter_or_right_mem hB₁_nd ha₁_not1 hv1, filter_flatMap_pair_not_mem ha₁_not0 hv0]
          simp [hba, hba.symm]
        · have hv1 : b ∉ B₁ := fun h => hadj ((hB₁_mem b).mp h).2
          have hv0 : b ∈ B₀ := (hB₀_mem b).mpr ⟨hb, hadj⟩
          simp only [hadj, false_iff, Alternate, hfw]
          rw [filter_or_not_mem ha₁_not1 hv1, filter_flatMap_pair_right hB₀_nd ha₁_not0 hv0]
          simp
      by_cases hu : u = a₁
      · subst u
        exact h_a1_b v ((hmem v).resolve_left (by simp [huv.symm]))
      · by_cases hv : v = a₁
        · subst v
          exact hsym a₁ u (Ne.symm hu) (h_a1_b u ((hmem u).resolve_left (by simp [hu])))
        · have huB : u ∈ B := (hmem u).resolve_left (by simp [hu])
          have hvB : v ∈ B := (hmem v).resolve_left (by simp [hv])
          have hno : ¬ G.Adj u v := hB_ind u huB v hvB
          have ha_nil : [a₁].filter (fun z => decide (z = u ∨ z = v)) = [] := by
            simp [Ne.symm hu, Ne.symm hv]
          simp only [hno, false_iff, Alternate, hfw, ha_nil, List.nil_append, List.append_nil]
          by_cases hu1 : G.Adj a₁ u <;> by_cases hv1 : G.Adj a₁ v
          · have huM : u ∈ B₁ := (hB₁_mem u).mpr ⟨huB, hu1⟩
            have hvM : v ∈ B₁ := (hB₁_mem v).mpr ⟨hvB, hv1⟩
            have hu0 : u ∉ B₀ := fun h => ((hB₀_mem u).mp h).2 hu1
            have hv0 : v ∉ B₀ := fun h => ((hB₀_mem v).mp h).2 hv1
            rw [filter_flatMap_pair_not_mem hu0 hv0, List.append_nil]
            rcases filter_or_both_mem hB₁_nd huM hvM huv with h | h <;> (rw [h]; simp)
          · have huM : u ∈ B₁ := (hB₁_mem u).mpr ⟨huB, hu1⟩
            have hvM : v ∉ B₁ := fun h => hv1 ((hB₁_mem v).mp h).2
            have hu0 : u ∉ B₀ := fun h => ((hB₀_mem u).mp h).2 hu1
            have hv0 : v ∈ B₀ := (hB₀_mem v).mpr ⟨hvB, hv1⟩
            rw [filter_or_left_mem hB₁_nd huM hvM, filter_flatMap_pair_right hB₀_nd hu0 hv0]
            simp
          · have huM : u ∉ B₁ := fun h => hu1 ((hB₁_mem u).mp h).2
            have hvM : v ∈ B₁ := (hB₁_mem v).mpr ⟨hvB, hv1⟩
            have hu0 : u ∈ B₀ := (hB₀_mem u).mpr ⟨huB, hu1⟩
            have hv0 : v ∉ B₀ := fun h => ((hB₀_mem v).mp h).2 hv1
            rw [filter_or_right_mem hB₁_nd huM hvM, filter_flatMap_pair_left hB₀_nd hu0 hv0]
            simp
          · have huM : u ∉ B₁ := fun h => hu1 ((hB₁_mem u).mp h).2
            have hvM : v ∉ B₁ := fun h => hv1 ((hB₁_mem v).mp h).2
            have hu0 : u ∈ B₀ := (hB₀_mem u).mpr ⟨huB, hu1⟩
            have hv0 : v ∈ B₀ := (hB₀_mem v).mpr ⟨hvB, hv1⟩
            rw [filter_or_not_mem huM hvM]
            simp only [List.reverse_nil, List.nil_append]
            rcases filter_flatMap_pair_both hB₀_nd hu0 hv0 huv with h | h <;> (rw [h]; simp)
  · -- Case |A| = 2
    obtain ⟨a₁, a₂, ha12, rfl⟩ := Finset.card_eq_two.mp hA2
    have ha₁_notB : a₁ ∉ B := hnotB a₁ (by simp)
    have ha₂_notB : a₂ ∉ B := hnotB a₂ (by simp)
    let B₁₂ := (B.filter (fun b => G.Adj a₁ b ∧ G.Adj a₂ b)).toList
    let B₁  := (B.filter (fun b => G.Adj a₁ b ∧ ¬ G.Adj a₂ b)).toList
    let B₂  := (B.filter (fun b => ¬ G.Adj a₁ b ∧ G.Adj a₂ b)).toList
    let B₀  := (B.filter (fun b => ¬ G.Adj a₁ b ∧ ¬ G.Adj a₂ b)).toList
    have hB₁₂_nd : B₁₂.Nodup := Finset.nodup_toList _
    have hB₁_nd : B₁.Nodup := Finset.nodup_toList _
    have hB₂_nd : B₂.Nodup := Finset.nodup_toList _
    have hB₀_nd : B₀.Nodup := Finset.nodup_toList _
    have hB₁₂_m : ∀ x, x ∈ B₁₂ ↔ x ∈ B ∧ G.Adj a₁ x ∧ G.Adj a₂ x := by intro x; simp [B₁₂]
    have hB₁_m : ∀ x, x ∈ B₁ ↔ x ∈ B ∧ G.Adj a₁ x ∧ ¬ G.Adj a₂ x := by intro x; simp [B₁]
    have hB₂_m : ∀ x, x ∈ B₂ ↔ x ∈ B ∧ ¬ G.Adj a₁ x ∧ G.Adj a₂ x := by intro x; simp [B₂]
    have hB₀_m : ∀ x, x ∈ B₀ ↔ x ∈ B ∧ ¬ G.Adj a₁ x ∧ ¬ G.Adj a₂ x := by intro x; simp [B₀]
    let w : List V :=
      [a₁] ++ B₁₂ ++ B₁ ++ [a₁] ++ B₁.reverse ++ B₂.reverse ++ [a₂] ++ B₂ ++ B₁₂.reverse ++ [a₂] ++
        B₀.flatMap (fun x => [x, x])
    refine ⟨w, ?_, ?_⟩
    · intro v
      simp only [w, List.count_append, List.count_reverse, count_flatMap_pair,
        List.Nodup.count hB₁₂_nd, List.Nodup.count hB₁_nd, List.Nodup.count hB₂_nd,
        List.Nodup.count hB₀_nd, List.count_singleton]
      by_cases hv1 : v = a₁
      · subst v
        have m12 : a₁ ∉ B₁₂ := fun h => ha₁_notB ((hB₁₂_m _).mp h).1
        have m1 : a₁ ∉ B₁ := fun h => ha₁_notB ((hB₁_m _).mp h).1
        have m2 : a₁ ∉ B₂ := fun h => ha₁_notB ((hB₂_m _).mp h).1
        have m0 : a₁ ∉ B₀ := fun h => ha₁_notB ((hB₀_m _).mp h).1
        simp [Ne.symm ha12, m12, m1, m2, m0]
      · by_cases hv2 : v = a₂
        · subst v
          have m12 : a₂ ∉ B₁₂ := fun h => ha₂_notB ((hB₁₂_m _).mp h).1
          have m1 : a₂ ∉ B₁ := fun h => ha₂_notB ((hB₁_m _).mp h).1
          have m2 : a₂ ∉ B₂ := fun h => ha₂_notB ((hB₂_m _).mp h).1
          have m0 : a₂ ∉ B₀ := fun h => ha₂_notB ((hB₀_m _).mp h).1
          simp [ha12, m12, m1, m2, m0]
        · have hvB : v ∈ B := (hmem v).resolve_left (by simp [hv1, hv2])
          by_cases e1 : G.Adj a₁ v <;> by_cases e2 : G.Adj a₂ v
          · have m12 : v ∈ B₁₂ := (hB₁₂_m _).mpr ⟨hvB, e1, e2⟩
            have m1 : v ∉ B₁ := fun h => ((hB₁_m _).mp h).2.2 e2
            have m2 : v ∉ B₂ := fun h => ((hB₂_m _).mp h).2.1 e1
            have m0 : v ∉ B₀ := fun h => ((hB₀_m _).mp h).2.1 e1
            simp [Ne.symm hv1, Ne.symm hv2, m12, m1, m2, m0]
          · have m12 : v ∉ B₁₂ := fun h => e2 ((hB₁₂_m _).mp h).2.2
            have m1 : v ∈ B₁ := (hB₁_m _).mpr ⟨hvB, e1, e2⟩
            have m2 : v ∉ B₂ := fun h => ((hB₂_m _).mp h).2.1 e1
            have m0 : v ∉ B₀ := fun h => ((hB₀_m _).mp h).2.1 e1
            simp [Ne.symm hv1, Ne.symm hv2, m12, m1, m2, m0]
          · have m12 : v ∉ B₁₂ := fun h => e1 ((hB₁₂_m _).mp h).2.1
            have m1 : v ∉ B₁ := fun h => e1 ((hB₁_m _).mp h).2.1
            have m2 : v ∈ B₂ := (hB₂_m _).mpr ⟨hvB, e1, e2⟩
            have m0 : v ∉ B₀ := fun h => ((hB₀_m _).mp h).2.2 e2
            simp [Ne.symm hv1, Ne.symm hv2, m12, m1, m2, m0]
          · have m12 : v ∉ B₁₂ := fun h => e1 ((hB₁₂_m _).mp h).2.1
            have m1 : v ∉ B₁ := fun h => e1 ((hB₁_m _).mp h).2.1
            have m2 : v ∉ B₂ := fun h => e2 ((hB₂_m _).mp h).2.2
            have m0 : v ∈ B₀ := (hB₀_m _).mpr ⟨hvB, e1, e2⟩
            simp [Ne.symm hv1, Ne.symm hv2, m12, m1, m2, m0]
    · have hfw (x y : V) :
          w.filter (fun z => decide (z = x ∨ z = y)) =
            ([a₁].filter (fun z => decide (z = x ∨ z = y))) ++
            (B₁₂.filter (fun z => decide (z = x ∨ z = y))) ++
            (B₁.filter (fun z => decide (z = x ∨ z = y))) ++
            ([a₁].filter (fun z => decide (z = x ∨ z = y))) ++
            (B₁.filter (fun z => decide (z = x ∨ z = y))).reverse ++
            (B₂.filter (fun z => decide (z = x ∨ z = y))).reverse ++
            ([a₂].filter (fun z => decide (z = x ∨ z = y))) ++
            (B₂.filter (fun z => decide (z = x ∨ z = y))) ++
            (B₁₂.filter (fun z => decide (z = x ∨ z = y))).reverse ++
            ([a₂].filter (fun z => decide (z = x ∨ z = y))) ++
            ((B₀.flatMap (fun t => [t, t])).filter (fun z => decide (z = x ∨ z = y))) := by
        simp only [w, List.filter_append, List.filter_reverse]
      have hsym : ∀ x y : V, x ≠ y → (G.Adj x y ↔ Alternate w x y) → (G.Adj y x ↔ Alternate w y x) := by
        intro x y _ hxy
        have hf : (fun z : V => decide (z = y ∨ z = x)) = (fun z => decide (z = x ∨ z = y)) := by
          funext z; simp [or_comm]
        rw [SimpleGraph.adj_comm, hxy]
        unfold Alternate
        rw [hf]
      have ha1_not (L : List V) (hL : ∀ x ∈ L, x ∈ B) : a₁ ∉ L := fun h => ha₁_notB (hL a₁ h)
      have ha2_not (L : List V) (hL : ∀ x ∈ L, x ∈ B) : a₂ ∉ L := fun h => ha₂_notB (hL a₂ h)
      have ha1_12 : a₁ ∉ B₁₂ := ha1_not _ (fun x h => ((hB₁₂_m x).mp h).1)
      have ha1_1 : a₁ ∉ B₁ := ha1_not _ (fun x h => ((hB₁_m x).mp h).1)
      have ha1_2 : a₁ ∉ B₂ := ha1_not _ (fun x h => ((hB₂_m x).mp h).1)
      have ha1_0 : a₁ ∉ B₀ := ha1_not _ (fun x h => ((hB₀_m x).mp h).1)
      have ha2_12 : a₂ ∉ B₁₂ := ha2_not _ (fun x h => ((hB₁₂_m x).mp h).1)
      have ha2_1 : a₂ ∉ B₁ := ha2_not _ (fun x h => ((hB₁_m x).mp h).1)
      have ha2_2 : a₂ ∉ B₂ := ha2_not _ (fun x h => ((hB₂_m x).mp h).1)
      have ha2_0 : a₂ ∉ B₀ := ha2_not _ (fun x h => ((hB₀_m x).mp h).1)
      have h_a1_b : ∀ b ∈ B, G.Adj a₁ b ↔ Alternate w a₁ b := by
        intro b hb
        have hba1 : a₁ ≠ b := fun h => ha₁_notB (h ▸ hb)
        have hba2 : a₂ ≠ b := fun h => ha₂_notB (h ▸ hb)
        have hf1 : [a₁].filter (fun z => decide (z = a₁ ∨ z = b)) = [a₁] := by simp
        have hf2 : [a₂].filter (fun z => decide (z = a₁ ∨ z = b)) = [] := by
          simp [Ne.symm ha12, hba2]
        unfold Alternate
        rw [hfw, hf1, hf2]
        by_cases e1 : G.Adj a₁ b <;> by_cases e2 : G.Adj a₂ b
        · have m12 : b ∈ B₁₂ := (hB₁₂_m _).mpr ⟨hb, e1, e2⟩
          have m1 : b ∉ B₁ := fun h => ((hB₁_m _).mp h).2.2 e2
          have m2 : b ∉ B₂ := fun h => ((hB₂_m _).mp h).2.1 e1
          have m0 : b ∉ B₀ := fun h => ((hB₀_m _).mp h).2.1 e1
          rw [filter_or_right_mem hB₁₂_nd ha1_12 m12, filter_or_not_mem ha1_1 m1,
            filter_or_not_mem ha1_2 m2, filter_flatMap_pair_not_mem ha1_0 m0]
          simp [e1, hba1, hba1.symm]
        · have m12 : b ∉ B₁₂ := fun h => e2 ((hB₁₂_m _).mp h).2.2
          have m1 : b ∈ B₁ := (hB₁_m _).mpr ⟨hb, e1, e2⟩
          have m2 : b ∉ B₂ := fun h => ((hB₂_m _).mp h).2.1 e1
          have m0 : b ∉ B₀ := fun h => ((hB₀_m _).mp h).2.1 e1
          rw [filter_or_not_mem ha1_12 m12, filter_or_right_mem hB₁_nd ha1_1 m1,
            filter_or_not_mem ha1_2 m2, filter_flatMap_pair_not_mem ha1_0 m0]
          simp [e1, hba1, hba1.symm]
        · have m12 : b ∉ B₁₂ := fun h => e1 ((hB₁₂_m _).mp h).2.1
          have m1 : b ∉ B₁ := fun h => e1 ((hB₁_m _).mp h).2.1
          have m2 : b ∈ B₂ := (hB₂_m _).mpr ⟨hb, e1, e2⟩
          have m0 : b ∉ B₀ := fun h => ((hB₀_m _).mp h).2.2 e2
          rw [filter_or_not_mem ha1_12 m12, filter_or_not_mem ha1_1 m1,
            filter_or_right_mem hB₂_nd ha1_2 m2, filter_flatMap_pair_not_mem ha1_0 m0]
          simp [e1]
        · have m12 : b ∉ B₁₂ := fun h => e1 ((hB₁₂_m _).mp h).2.1
          have m1 : b ∉ B₁ := fun h => e1 ((hB₁_m _).mp h).2.1
          have m2 : b ∉ B₂ := fun h => e2 ((hB₂_m _).mp h).2.2
          have m0 : b ∈ B₀ := (hB₀_m _).mpr ⟨hb, e1, e2⟩
          rw [filter_or_not_mem ha1_12 m12, filter_or_not_mem ha1_1 m1,
            filter_or_not_mem ha1_2 m2, filter_flatMap_pair_right hB₀_nd ha1_0 m0]
          simp [e1]
      have h_a2_b : ∀ b ∈ B, G.Adj a₂ b ↔ Alternate w a₂ b := by
        intro b hb
        have hba1 : a₁ ≠ b := fun h => ha₁_notB (h ▸ hb)
        have hba2 : a₂ ≠ b := fun h => ha₂_notB (h ▸ hb)
        have hf1 : [a₁].filter (fun z => decide (z = a₂ ∨ z = b)) = [] := by
          simp [ha12, hba1]
        have hf2 : [a₂].filter (fun z => decide (z = a₂ ∨ z = b)) = [a₂] := by simp
        unfold Alternate
        rw [hfw, hf1, hf2]
        by_cases e1 : G.Adj a₁ b <;> by_cases e2 : G.Adj a₂ b
        · have m12 : b ∈ B₁₂ := (hB₁₂_m _).mpr ⟨hb, e1, e2⟩
          have m1 : b ∉ B₁ := fun h => ((hB₁_m _).mp h).2.2 e2
          have m2 : b ∉ B₂ := fun h => ((hB₂_m _).mp h).2.1 e1
          have m0 : b ∉ B₀ := fun h => ((hB₀_m _).mp h).2.1 e1
          rw [filter_or_right_mem hB₁₂_nd ha2_12 m12, filter_or_not_mem ha2_1 m1,
            filter_or_not_mem ha2_2 m2, filter_flatMap_pair_not_mem ha2_0 m0]
          simp [e2, hba2, hba2.symm]
        · have m12 : b ∉ B₁₂ := fun h => e2 ((hB₁₂_m _).mp h).2.2
          have m1 : b ∈ B₁ := (hB₁_m _).mpr ⟨hb, e1, e2⟩
          have m2 : b ∉ B₂ := fun h => ((hB₂_m _).mp h).2.1 e1
          have m0 : b ∉ B₀ := fun h => ((hB₀_m _).mp h).2.1 e1
          rw [filter_or_not_mem ha2_12 m12, filter_or_right_mem hB₁_nd ha2_1 m1,
            filter_or_not_mem ha2_2 m2, filter_flatMap_pair_not_mem ha2_0 m0]
          simp [e2]
        · have m12 : b ∉ B₁₂ := fun h => e1 ((hB₁₂_m _).mp h).2.1
          have m1 : b ∉ B₁ := fun h => e1 ((hB₁_m _).mp h).2.1
          have m2 : b ∈ B₂ := (hB₂_m _).mpr ⟨hb, e1, e2⟩
          have m0 : b ∉ B₀ := fun h => ((hB₀_m _).mp h).2.2 e2
          rw [filter_or_not_mem ha2_12 m12, filter_or_not_mem ha2_1 m1,
            filter_or_right_mem hB₂_nd ha2_2 m2, filter_flatMap_pair_not_mem ha2_0 m0]
          simp [e2, hba2, hba2.symm]
        · have m12 : b ∉ B₁₂ := fun h => e1 ((hB₁₂_m _).mp h).2.1
          have m1 : b ∉ B₁ := fun h => e1 ((hB₁_m _).mp h).2.1
          have m2 : b ∉ B₂ := fun h => e2 ((hB₂_m _).mp h).2.2
          have m0 : b ∈ B₀ := (hB₀_m _).mpr ⟨hb, e1, e2⟩
          rw [filter_or_not_mem ha2_12 m12, filter_or_not_mem ha2_1 m1,
            filter_or_not_mem ha2_2 m2, filter_flatMap_pair_right hB₀_nd ha2_0 m0]
          simp [e2]
      have h_a1_a2 : G.Adj a₁ a₂ ↔ Alternate w a₁ a₂ := by
        have hno : ¬ G.Adj a₁ a₂ := hA_ind a₁ (by simp) a₂ (by simp)
        simp only [hno, false_iff, Alternate, hfw]
        rw [filter_or_not_mem ha1_12 ha2_12, filter_or_not_mem ha1_1 ha2_1,
          filter_or_not_mem ha1_2 ha2_2, filter_flatMap_pair_not_mem ha1_0 ha2_0]
        simp
      intro u v huv
      by_cases hu1 : u = a₁
      · subst u
        by_cases hv2 : v = a₂
        · subst v; exact h_a1_a2
        · exact h_a1_b v ((hmem v).resolve_left (by simp [huv.symm, hv2]))
      · by_cases hu2 : u = a₂
        · subst u
          by_cases hv1 : v = a₁
          · subst v; exact hsym a₁ a₂ ha12 h_a1_a2
          · exact h_a2_b v ((hmem v).resolve_left (by simp [hv1, huv.symm]))
        · by_cases hv1 : v = a₁
          · subst v
            exact hsym a₁ u (Ne.symm hu1) (h_a1_b u ((hmem u).resolve_left (by simp [hu1, hu2])))
          · by_cases hv2 : v = a₂
            · subst v
              exact hsym a₂ u (Ne.symm hu2) (h_a2_b u ((hmem u).resolve_left (by simp [hu1, hu2])))
            · have huB : u ∈ B := (hmem u).resolve_left (by simp [hu1, hu2])
              have hvB : v ∈ B := (hmem v).resolve_left (by simp [hv1, hv2])
              have hno : ¬ G.Adj u v := hB_ind u huB v hvB
              have hf1 : [a₁].filter (fun z => decide (z = u ∨ z = v)) = [] := by
                simp [Ne.symm hu1, Ne.symm hv1]
              have hf2 : [a₂].filter (fun z => decide (z = u ∨ z = v)) = [] := by
                simp [Ne.symm hu2, Ne.symm hv2]
              simp only [hno, false_iff, Alternate, hfw, hf1, hf2]
              by_cases eu1 : G.Adj a₁ u <;> by_cases eu2 : G.Adj a₂ u <;>
                by_cases ev1 : G.Adj a₁ v <;> by_cases ev2 : G.Adj a₂ v
              · have huM : u ∈ B₁₂ := (hB₁₂_m _).mpr ⟨huB, eu1, eu2⟩
                have hvM : v ∈ B₁₂ := (hB₁₂_m _).mpr ⟨hvB, ev1, ev2⟩
                rw [filter_or_not_mem (fun h => ((hB₁_m _).mp h).2.2 eu2) (fun h => ((hB₁_m _).mp h).2.2 ev2),
                    filter_or_not_mem (fun h => ((hB₂_m _).mp h).2.1 eu1) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.1 eu1) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                rcases filter_or_both_mem hB₁₂_nd huM hvM huv with h | h <;> (rw [h]; simp)
              · rw [filter_or_left_mem hB₁₂_nd ((hB₁₂_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ev2 ((hB₁₂_m _).mp h).2.2),
                    filter_or_right_mem hB₁_nd (fun h => ((hB₁_m _).mp h).2.2 eu2) ((hB₁_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_or_not_mem (fun h => ((hB₂_m _).mp h).2.1 eu1) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.1 eu1) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                simp
              · rw [filter_or_left_mem hB₁₂_nd ((hB₁₂_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_not_mem (fun h => ((hB₁_m _).mp h).2.2 eu2) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_or_right_mem hB₂_nd (fun h => ((hB₂_m _).mp h).2.1 eu1) ((hB₂_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.1 eu1) (fun h => ((hB₀_m _).mp h).2.2 ev2)]
                simp
              · rw [filter_or_left_mem hB₁₂_nd ((hB₁₂_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_not_mem (fun h => ((hB₁_m _).mp h).2.2 eu2) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_or_not_mem (fun h => ((hB₂_m _).mp h).2.1 eu1) (fun h => ev2 ((hB₂_m _).mp h).2.2),
                    filter_flatMap_pair_right hB₀_nd (fun h => ((hB₀_m _).mp h).2.1 eu1) ((hB₀_m _).mpr ⟨hvB, ev1, ev2⟩)]
                simp
              · rw [filter_or_right_mem hB₁₂_nd (fun h => eu2 ((hB₁₂_m _).mp h).2.2) ((hB₁₂_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_or_left_mem hB₁_nd ((hB₁_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ((hB₁_m _).mp h).2.2 ev2),
                    filter_or_not_mem (fun h => ((hB₂_m _).mp h).2.1 eu1) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.1 eu1) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                simp
              · rw [filter_or_not_mem (fun h => eu2 ((hB₁₂_m _).mp h).2.2) (fun h => ev2 ((hB₁₂_m _).mp h).2.2),
                    filter_or_not_mem (fun h => ((hB₂_m _).mp h).2.1 eu1) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.1 eu1) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                rcases filter_or_both_mem hB₁_nd ((hB₁_m _).mpr ⟨huB, eu1, eu2⟩) ((hB₁_m _).mpr ⟨hvB, ev1, ev2⟩) huv with h | h <;> (rw [h]; simp)
              · rw [filter_or_not_mem (fun h => eu2 ((hB₁₂_m _).mp h).2.2) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_left_mem hB₁_nd ((hB₁_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_or_right_mem hB₂_nd (fun h => ((hB₂_m _).mp h).2.1 eu1) ((hB₂_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.1 eu1) (fun h => ((hB₀_m _).mp h).2.2 ev2)]
                simp
              · rw [filter_or_not_mem (fun h => eu2 ((hB₁₂_m _).mp h).2.2) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_left_mem hB₁_nd ((hB₁_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_or_not_mem (fun h => ((hB₂_m _).mp h).2.1 eu1) (fun h => ev2 ((hB₂_m _).mp h).2.2),
                    filter_flatMap_pair_right hB₀_nd (fun h => ((hB₀_m _).mp h).2.1 eu1) ((hB₀_m _).mpr ⟨hvB, ev1, ev2⟩)]
                simp
              · rw [filter_or_right_mem hB₁₂_nd (fun h => eu1 ((hB₁₂_m _).mp h).2.1) ((hB₁₂_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_or_not_mem (fun h => eu1 ((hB₁_m _).mp h).2.1) (fun h => ((hB₁_m _).mp h).2.2 ev2),
                    filter_or_left_mem hB₂_nd ((hB₂_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.2 eu2) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                simp
              · rw [filter_or_not_mem (fun h => eu1 ((hB₁₂_m _).mp h).2.1) (fun h => ev2 ((hB₁₂_m _).mp h).2.2),
                    filter_or_right_mem hB₁_nd (fun h => eu1 ((hB₁_m _).mp h).2.1) ((hB₁_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_or_left_mem hB₂_nd ((hB₂_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.2 eu2) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                simp
              · rw [filter_or_not_mem (fun h => eu1 ((hB₁₂_m _).mp h).2.1) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_not_mem (fun h => eu1 ((hB₁_m _).mp h).2.1) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_flatMap_pair_not_mem (fun h => ((hB₀_m _).mp h).2.2 eu2) (fun h => ((hB₀_m _).mp h).2.2 ev2)]
                rcases filter_or_both_mem hB₂_nd ((hB₂_m _).mpr ⟨huB, eu1, eu2⟩) ((hB₂_m _).mpr ⟨hvB, ev1, ev2⟩) huv with h | h <;> (rw [h]; simp)
              · rw [filter_or_not_mem (fun h => eu1 ((hB₁₂_m _).mp h).2.1) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_not_mem (fun h => eu1 ((hB₁_m _).mp h).2.1) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_or_left_mem hB₂_nd ((hB₂_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ev2 ((hB₂_m _).mp h).2.2),
                    filter_flatMap_pair_right hB₀_nd (fun h => ((hB₀_m _).mp h).2.2 eu2) ((hB₀_m _).mpr ⟨hvB, ev1, ev2⟩)]
                simp
              · rw [filter_or_right_mem hB₁₂_nd (fun h => eu1 ((hB₁₂_m _).mp h).2.1) ((hB₁₂_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_or_not_mem (fun h => eu1 ((hB₁_m _).mp h).2.1) (fun h => ((hB₁_m _).mp h).2.2 ev2),
                    filter_or_not_mem (fun h => eu2 ((hB₂_m _).mp h).2.2) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_left hB₀_nd ((hB₀_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                simp
              · rw [filter_or_not_mem (fun h => eu1 ((hB₁₂_m _).mp h).2.1) (fun h => ev2 ((hB₁₂_m _).mp h).2.2),
                    filter_or_right_mem hB₁_nd (fun h => eu1 ((hB₁_m _).mp h).2.1) ((hB₁_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_or_not_mem (fun h => eu2 ((hB₂_m _).mp h).2.2) (fun h => ((hB₂_m _).mp h).2.1 ev1),
                    filter_flatMap_pair_left hB₀_nd ((hB₀_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ((hB₀_m _).mp h).2.1 ev1)]
                simp
              · rw [filter_or_not_mem (fun h => eu1 ((hB₁₂_m _).mp h).2.1) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_not_mem (fun h => eu1 ((hB₁_m _).mp h).2.1) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_or_right_mem hB₂_nd (fun h => eu2 ((hB₂_m _).mp h).2.2) ((hB₂_m _).mpr ⟨hvB, ev1, ev2⟩),
                    filter_flatMap_pair_left hB₀_nd ((hB₀_m _).mpr ⟨huB, eu1, eu2⟩) (fun h => ((hB₀_m _).mp h).2.2 ev2)]
                simp
              · rw [filter_or_not_mem (fun h => eu1 ((hB₁₂_m _).mp h).2.1) (fun h => ev1 ((hB₁₂_m _).mp h).2.1),
                    filter_or_not_mem (fun h => eu1 ((hB₁_m _).mp h).2.1) (fun h => ev1 ((hB₁_m _).mp h).2.1),
                    filter_or_not_mem (fun h => eu2 ((hB₂_m _).mp h).2.2) (fun h => ev2 ((hB₂_m _).mp h).2.2)]
                rcases filter_flatMap_pair_both hB₀_nd ((hB₀_m _).mpr ⟨huB, eu1, eu2⟩) ((hB₀_m _).mpr ⟨hvB, ev1, ev2⟩) huv with h | h <;> (rw [h]; simp)

/-! ### Part 3: Verified finite certificate for all 512 `(3, 3)` bipartite graphs on `Fin 6` -/

private def wordBlk0 : ℕ → ℕ
  | 0 => 858330165
  | 1 => 858428920
  | 2 => 858476865
  | 3 => 858455855
  | 4 => 858524565
  | 5 => 858463840
  | 6 => 858510525
  | 7 => 858461535
  | 8 => 846959320
  | 9 => 861947560
  | 10 => 861955055
  | 11 => 861951635
  | 12 => 861963040
  | 13 => 861952960
  | 14 => 861960735
  | 15 => 861952570
  | 16 => 847007265
  | 17 => 863626715
  | 18 => 863634945
  | 19 => 863637695
  | 20 => 863642685
  | 21 => 863632570
  | 22 => 863640345
  | 23 => 863638665
  | 24 => 846979775
  | 25 => 851640875
  | 26 => 853326935
  | 27 => 862815275
  | 28 => 855000095
  | 29 => 864214090
  | 30 => 862815705
  | 31 => 862815425
  | _ => 0

private def wordBlk1 : ℕ → ℕ
  | 0 => 847054965
  | 1 => 865306360
  | 2 => 865314345
  | 3 => 865310855
  | 4 => 865322085
  | 5 => 865325080
  | 6 => 865326405
  | 7 => 865325835
  | 8 => 846987760
  | 9 => 851642200
  | 10 => 853321810
  | 11 => 865893485
  | 12 => 855014320
  | 13 => 863096500
  | 14 => 863096715
  | 15 => 863096620
  | 16 => 847034445
  | 17 => 851649975
  | 18 => 853329585
  | 19 => 866174495
  | 20 => 855015645
  | 21 => 864776110
  | 22 => 864776325
  | 23 => 864776415
  | 24 => 846984375
  | 25 => 851641630
  | 26 => 853327725
  | 27 => 852698855
  | 28 => 855014895
  | 29 => 852980050
  | 30 => 854659845
  | 31 => 863005050
  | _ => 0

private def wordBlk2 : ℕ → ℕ
  | 0 => 423983800
  | 1 => 449041960
  | 2 => 449049455
  | 3 => 449046035
  | 4 => 449057440
  | 5 => 449047360
  | 6 => 449055135
  | 7 => 449046970
  | 8 => 25826680
  | 9 => 517626280
  | 10 => 929719475
  | 11 => 517630355
  | 12 => 929720800
  | 13 => 517631680
  | 14 => 929720410
  | 15 => 517631290
  | 16 => 25834175
  | 17 => 928001195
  | 18 => 615879215
  | 19 => 929999915
  | 20 => 930000735
  | 21 => 930025985
  | 22 => 619056185
  | 23 => 930000065
  | 24 => 25829675
  | 25 => 154600235
  | 26 => 928281455
  | 27 => 518493995
  | 28 => 928588690
  | 29 => 630467530
  | 30 => 929862905
  | 31 => 518494145
  | _ => 0

private def wordBlk3 : ℕ → ℕ
  | 0 => 25842160
  | 1 => 928002520
  | 2 => 930279345
  | 3 => 930313660
  | 4 => 676625320
  | 5 => 930281140
  | 6 => 679522540
  | 7 => 930281260
  | 8 => 25831000
  | 9 => 154601560
  | 10 => 928301015
  | 11 => 690933485
  | 12 => 928562680
  | 13 => 518775220
  | 14 => 929909740
  | 15 => 518775340
  | 16 => 25838775
  | 17 => 928001950
  | 18 => 246182735
  | 19 => 928176815
  | 20 => 306649090
  | 21 => 928223650
  | 22 => 930189675
  | 23 => 930189690
  | 24 => 25830430
  | 25 => 154600990
  | 26 => 928281575
  | 27 => 155658215
  | 28 => 928562770
  | 29 => 155939410
  | 30 => 928503595
  | 31 => 518683770
  | _ => 0

private def wordBlk4 : ℕ → ℕ
  | 0 => 424031745
  | 1 => 450721115
  | 2 => 450729345
  | 3 => 450732095
  | 4 => 450737085
  | 5 => 450726970
  | 6 => 450734745
  | 7 => 450733065
  | 8 => 27505835
  | 9 => 555134435
  | 10 => 988745975
  | 11 => 990185075
  | 12 => 990186970
  | 13 => 558877505
  | 14 => 990204665
  | 15 => 990185225
  | 16 => 27514065
  | 17 => 990464255
  | 18 => 527711745
  | 19 => 527714495
  | 20 => 990466905
  | 21 => 990465225
  | 22 => 527717145
  | 23 => 527715465
  | 24 => 27515735
  | 25 => 988466615
  | 26 => 164684375
  | 27 => 528290675
  | 28 => 989055045
  | 29 => 990562145
  | 30 => 571682265
  | 31 => 528290825
  | _ => 0

private def wordBlk5 : ℕ → ℕ
  | 0 => 27521805
  | 1 => 990744190
  | 2 => 988748625
  | 3 => 990780015
  | 4 => 676626645
  | 5 => 679810215
  | 6 => 990747525
  | 7 => 990747615
  | 8 => 27510610
  | 9 => 186004055
  | 10 => 988746765
  | 11 => 988876055
  | 12 => 306936765
  | 13 => 990375880
  | 14 => 988969725
  | 15 => 990375900
  | 16 => 27518385
  | 17 => 988479695
  | 18 => 164687025
  | 19 => 692614175
  | 20 => 989029065
  | 21 => 990655815
  | 22 => 528853125
  | 23 => 528853215
  | 24 => 27516525
  | 25 => 988466735
  | 26 => 164685165
  | 27 => 165454895
  | 28 => 989029125
  | 29 => 988689805
  | 30 => 166017285
  | 31 => 528481500
  | _ => 0

private def wordBlk6 : ℕ → ℕ
  | 0 => 423997775
  | 1 => 428424515
  | 2 => 430110575
  | 3 => 449676395
  | 4 => 431783735
  | 5 => 451075210
  | 6 => 449676825
  | 7 => 449676545
  | 8 => 15518915
  | 9 => 92501315
  | 10 => 555414515
  | 11 => 819191915
  | 12 => 555715240
  | 13 => 982953610
  | 14 => 558675545
  | 15 => 819192065
  | 16 => 17204975
  | 17 => 615599675
  | 18 => 102585455
  | 19 => 828988595
  | 20 => 616181595
  | 21 => 619374785
  | 22 => 924168345
  | 23 => 828988745
  | 24 => 26420975
  | 25 => 757053935
  | 26 => 766850615
  | 27 => 521293355
  | 28 => 306734375
  | 29 => 529690570
  | 30 => 521293785
  | 31 => 521293505
  | _ => 0

private def wordBlk7 : ℕ → ℕ
  | 0 => 18878135
  | 1 => 184566760
  | 2 => 245033115
  | 3 => 679607825
  | 4 => 676625715
  | 5 => 676748680
  | 6 => 676795515
  | 7 => 679607850
  | 8 => 27819790
  | 9 => 972603790
  | 10 => 246501335
  | 11 => 166854670
  | 12 => 305561320
  | 13 => 116193845
  | 14 => 1001511420
  | 15 => 1002465780
  | 16 => 26421405
  | 17 => 185802095
  | 18 => 913818525
  | 19 => 158457885
  | 20 => 305608155
  | 21 => 951169590
  | 22 => 117874535
  | 23 => 952077510
  | 24 => 26421095
  | 25 => 757054055
  | 26 => 766850735
  | 27 => 158457575
  | 28 => 306734395
  | 29 => 1002504625
  | 30 => 952116355
  | 31 => 521483130
  | _ => 0

private def wordBlk8 : ℕ → ℕ
  | 0 => 424079445
  | 1 => 452400760
  | 2 => 452408745
  | 3 => 452405255
  | 4 => 452416485
  | 5 => 452419480
  | 6 => 452420805
  | 7 => 452420235
  | 8 => 29185480
  | 9 => 555135760
  | 10 => 1050651815
  | 11 => 559165180
  | 12 => 1049492080
  | 13 => 1050651460
  | 14 => 1050671020
  | 15 => 1050651580
  | 16 => 29193465
  | 17 => 1050930425
  | 18 => 615881865
  | 19 => 619631535
  | 20 => 1049493405
  | 21 => 1050958695
  | 22 => 1050932685
  | 23 => 1050932775
  | 24 => 29188895
  | 25 => 186291730
  | 26 => 246758085
  | 27 => 1050795185
  | 28 => 1049492655
  | 29 => 1049622130
  | 30 => 1049668965
  | 31 => 1050795210
  | _ => 0

private def wordBlk9 : ℕ → ℕ
  | 0 => 29201205
  | 1 => 1051210360
  | 2 => 1051211685
  | 3 => 1051211115
  | 4 => 537796965
  | 5 => 537799960
  | 6 => 537801285
  | 7 => 537800715
  | 8 => 29203120
  | 9 => 1048933000
  | 10 => 1049233725
  | 11 => 1051308220
  | 12 => 174769840
  | 13 => 538368580
  | 14 => 573362955
  | 15 => 538368700
  | 16 => 29204445
  | 17 => 1048946050
  | 18 => 1049214225
  | 19 => 1051355055
  | 20 => 174771165
  | 21 => 633828910
  | 22 => 538649805
  | 23 => 538649895
  | 24 => 29203695
  | 25 => 1048933090
  | 26 => 1049214285
  | 27 => 1049109115
  | 28 => 174770415
  | 29 => 175532770
  | 30 => 175813965
  | 31 => 538512330
  | _ => 0

private def wordBlk10 : ℕ → ℕ
  | 0 => 424005760
  | 1 => 428425840
  | 2 => 430105450
  | 3 => 452754605
  | 4 => 431797960
  | 5 => 449957620
  | 6 => 449957835
  | 7 => 449957740
  | 8 => 15520240
  | 9 => 92502640
  | 10 => 555427565
  | 11 => 1043419565
  | 12 => 555695740
  | 13 => 819473140
  | 14 => 558722380
  | 15 => 819473260
  | 16 => 17199850
  | 17 => 184279085
  | 18 => 615879825
  | 19 => 616002605
  | 20 => 305211795
  | 21 => 619188520
  | 22 => 616096275
  | 23 => 619188540
  | 24 => 29499185
  | 25 => 1033069745
  | 26 => 244815245
  | 27 => 106116370
  | 28 => 307247410
  | 29 => 176932145
  | 30 => 1061969790
  | 31 => 1062650730
  | _ => 0

private def wordBlk11 : ℕ → ℕ
  | 0 => 18892360
  | 1 => 676066060
  | 2 => 676360275
  | 3 => 680120860
  | 4 => 112670920
  | 5 => 839066500
  | 6 => 925849035
  | 7 => 839066620
  | 8 => 26702200
  | 9 => 757335160
  | 10 => 246315070
  | 11 => 539768045
  | 12 => 776928520
  | 13 => 522974260
  | 14 => 522974475
  | 15 => 522974380
  | 16 => 26702415
  | 17 => 185848930
  | 18 => 244908915
  | 19 => 961286130
  | 20 => 915499215
  | 21 => 160138575
  | 22 => 109477750
  | 23 => 961874190
  | 24 => 26702290
  | 25 => 757335250
  | 26 => 246315085
  | 27 => 1062689575
  | 28 => 776928610
  | 29 => 160138450
  | 30 => 961913035
  | 31 => 523115910
  | _ => 0

private def wordBlk12 : ℕ → ℕ
  | 0 => 424052445
  | 1 => 428433615
  | 2 => 430113225
  | 3 => 453035615
  | 4 => 431799285
  | 5 => 451637230
  | 6 => 451637445
  | 7 => 451637535
  | 8 => 15528015
  | 9 => 555135010
  | 10 => 244457765
  | 11 => 555303365
  | 12 => 304924120
  | 13 => 555350200
  | 14 => 559002315
  | 15 => 559002330
  | 16 => 17207625
  | 17 => 615606245
  | 18 => 102588105
  | 19 => 1045100255
  | 20 => 616162125
  | 21 => 619468455
  | 22 => 829551045
  | 23 => 829551135
  | 24 => 29780195
  | 25 => 184116005
  | 26 => 1034750435
  | 27 => 97719585
  | 28 => 307294245
  | 29 => 1072086330
  | 30 => 178612835
  | 31 => 1072447410
  | _ => 0

private def wordBlk13 : ℕ → ℕ
  | 0 => 18893685
  | 1 => 676072600
  | 2 => 676347285
  | 3 => 680167695
  | 4 => 112672245
  | 5 => 986314990
  | 6 => 839347725
  | 7 => 839347815
  | 8 => 28381810
  | 9 => 184162840
  | 10 => 246595005
  | 11 => 1021744500
  | 12 => 975965170
  | 13 => 99400275
  | 14 => 170216050
  | 15 => 1022059140
  | 16 => 28382025
  | 17 => 186128865
  | 18 => 767413065
  | 19 => 541448735
  | 20 => 777209745
  | 21 => 533051950
  | 22 => 533052165
  | 23 => 533052255
  | 24 => 28382085
  | 25 => 186128875
  | 26 => 767413125
  | 27 => 1072486255
  | 28 => 777209805
  | 29 => 1022097985
  | 30 => 170216325
  | 31 => 533146740
  | _ => 0

private def wordBlk14 : ℕ → ℕ
  | 0 => 424001295
  | 1 => 428425090
  | 2 => 430111185
  | 3 => 429443405
  | 4 => 431798355
  | 5 => 429724600
  | 6 => 431404395
  | 7 => 449827290
  | 8 => 15519490
  | 9 => 92501890
  | 10 => 555414605
  | 11 => 93520205
  | 12 => 555695800
  | 13 => 93801400
  | 14 => 555630140
  | 15 => 819342810
  | 16 => 17205585
  | 17 => 615599765
  | 18 => 102586065
  | 19 => 103316885
  | 20 => 616162155
  | 21 => 615816350
  | 22 => 103879275
  | 23 => 829140540
  | 24 => 16304525
  | 25 => 394218125
  | 26 => 404014805
  | 27 => 97719245
  | 28 => 305048300
  | 29 => 638074610
  | 30 => 587686340
  | 31 => 823541850
  | _ => 0

private def wordBlk15 : ℕ → ℕ
  | 0 => 18892755
  | 1 => 676066120
  | 2 => 676347315
  | 3 => 676235660
  | 4 => 112671315
  | 5 => 113394760
  | 6 => 113675955
  | 7 => 839171370
  | 8 => 16585720
  | 9 => 394499320
  | 10 => 244628990
  | 11 => 698259560
  | 12 => 414092680
  | 13 => 99400120
  | 14 => 597483020
  | 15 => 825174630
  | 16 => 18265515
  | 17 => 184442780
  | 18 => 404577195
  | 19 => 708056240
  | 20 => 414373875
  | 21 => 657667970
  | 22 => 109477995
  | 23 => 835205460
  | 24 => 26565355
  | 25 => 757198315
  | 26 => 766996045
  | 27 => 762797035
  | 28 => 777026875
  | 29 => 764429815
  | 30 => 774460645
  | 31 => 522182970
  | _ => 0

private def wordLookup (m : ℕ) : ℕ :=
  match m / 32 with
  | 0 => wordBlk0 (m % 32)
  | 1 => wordBlk1 (m % 32)
  | 2 => wordBlk2 (m % 32)
  | 3 => wordBlk3 (m % 32)
  | 4 => wordBlk4 (m % 32)
  | 5 => wordBlk5 (m % 32)
  | 6 => wordBlk6 (m % 32)
  | 7 => wordBlk7 (m % 32)
  | 8 => wordBlk8 (m % 32)
  | 9 => wordBlk9 (m % 32)
  | 10 => wordBlk10 (m % 32)
  | 11 => wordBlk11 (m % 32)
  | 12 => wordBlk12 (m % 32)
  | 13 => wordBlk13 (m % 32)
  | 14 => wordBlk14 (m % 32)
  | 15 => wordBlk15 (m % 32)
  | _ => 0

private def decodeWordAux : ℕ → ℕ → List (Fin 6)
  | 0, _ => []
  | k + 1, n => ⟨n % 6, Nat.mod_lt n (by decide)⟩ :: decodeWordAux k (n / 6)

private def decodeWord (n : ℕ) : List (Fin 6) := decodeWordAux 12 n

private def maskAdj (m : ℕ) (a b : Fin 6) : Bool :=
  if a.val < 3 ∧ 3 ≤ b.val then
    ((m / 2 ^ (3 * a.val + (b.val - 3))) % 2) == 1
  else if b.val < 3 ∧ 3 ≤ a.val then
    ((m / 2 ^ (3 * b.val + (a.val - 3))) % 2) == 1
  else false

private def isChainNe : List (Fin 6) → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => (x != y) && isChainNe (y :: t)

private lemma isChainNe_iff (l : List (Fin 6)) : isChainNe l = true ↔ List.IsChain (· ≠ ·) l := by
  induction l with
  | nil => simp [isChainNe]
  | cons x t ih =>
    cases t with
    | nil => simp [isChainNe]
    | cons y rest =>
      simp only [isChainNe, Bool.and_eq_true, bne_iff_ne, List.isChain_cons_cons, ih]

private def checkMask (m : ℕ) : Bool :=
  let w := decodeWord (wordLookup m)
  (List.finRange 6).all (fun v => w.count v == 2) &&
  (List.finRange 6).all (fun a =>
    (List.finRange 6).all (fun b =>
      (a == b) ||
      (maskAdj m a b == isChainNe (w.filter (fun x => decide (x = a ∨ x = b))))))

private def checkTree : ℕ → ℕ → Bool
  | 0, lo => checkMask lo
  | d + 1, lo => checkTree d lo && checkTree d (lo + 2 ^ d)

private lemma checkTree_spec (d : ℕ) : ∀ lo : ℕ, checkTree d lo = true →
    ∀ m, lo ≤ m → m < lo + 2 ^ d → checkMask m = true := by
  induction d with
  | zero =>
    intro lo h m h1 h2
    have hmeq : m = lo := by omega
    subst hmeq
    exact h
  | succ d ih =>
    intro lo h m h1 h2
    simp only [checkTree, Bool.and_eq_true] at h
    by_cases hlt : m < lo + 2 ^ d
    · exact ih lo h.1 m h1 hlt
    · exact ih (lo + 2 ^ d) h.2 m (by omega) (by rw [pow_succ] at h2; omega)

private lemma checkTree_0  : checkTree 5 0   = true := by decide
private lemma checkTree_1  : checkTree 5 32  = true := by decide
private lemma checkTree_2  : checkTree 5 64  = true := by decide
private lemma checkTree_3  : checkTree 5 96  = true := by decide
private lemma checkTree_4  : checkTree 5 128 = true := by decide
private lemma checkTree_5  : checkTree 5 160 = true := by decide
private lemma checkTree_6  : checkTree 5 192 = true := by decide
private lemma checkTree_7  : checkTree 5 224 = true := by decide
private lemma checkTree_8  : checkTree 5 256 = true := by decide
private lemma checkTree_9  : checkTree 5 288 = true := by decide
private lemma checkTree_10 : checkTree 5 320 = true := by decide
private lemma checkTree_11 : checkTree 5 352 = true := by decide
private lemma checkTree_12 : checkTree 5 384 = true := by decide
private lemma checkTree_13 : checkTree 5 416 = true := by decide
private lemma checkTree_14 : checkTree 5 448 = true := by decide
private lemma checkTree_15 : checkTree 5 480 = true := by decide

private lemma checkMask_all (m : ℕ) (hm : m < 512) : checkMask m = true := by
  have hblk : m / 32 < 16 := by omega
  have hmod : m = 32 * (m / 32) + m % 32 := by omega
  have hlo : 32 * (m / 32) ≤ m := by omega
  have hhi : m < 32 * (m / 32) + 2 ^ 5 := by omega
  generalize hk : m / 32 = k at hblk hlo hhi
  interval_cases k
  · exact checkTree_spec 5 0   checkTree_0  m hlo hhi
  · exact checkTree_spec 5 32  checkTree_1  m hlo hhi
  · exact checkTree_spec 5 64  checkTree_2  m hlo hhi
  · exact checkTree_spec 5 96  checkTree_3  m hlo hhi
  · exact checkTree_spec 5 128 checkTree_4  m hlo hhi
  · exact checkTree_spec 5 160 checkTree_5  m hlo hhi
  · exact checkTree_spec 5 192 checkTree_6  m hlo hhi
  · exact checkTree_spec 5 224 checkTree_7  m hlo hhi
  · exact checkTree_spec 5 256 checkTree_8  m hlo hhi
  · exact checkTree_spec 5 288 checkTree_9  m hlo hhi
  · exact checkTree_spec 5 320 checkTree_10 m hlo hhi
  · exact checkTree_spec 5 352 checkTree_11 m hlo hhi
  · exact checkTree_spec 5 384 checkTree_12 m hlo hhi
  · exact checkTree_spec 5 416 checkTree_13 m hlo hhi
  · exact checkTree_spec 5 448 checkTree_14 m hlo hhi
  · exact checkTree_spec 5 480 checkTree_15 m hlo hhi

private lemma bit_horner (c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℕ)
    (h0 : c0 ≤ 1) (h1 : c1 ≤ 1) (h2 : c2 ≤ 1) (h3 : c3 ≤ 1) (h4 : c4 ≤ 1)
    (h5 : c5 ≤ 1) (h6 : c6 ≤ 1) (h7 : c7 ≤ 1) (h8 : c8 ≤ 1) :
    let m := c0 + 2 * (c1 + 2 * (c2 + 2 * (c3 + 2 * (c4 + 2 * (c5 + 2 * (c6 + 2 * (c7 + 2 * c8)))))))
    m < 512 ∧
    m / 1 % 2 = c0 ∧ m / 2 % 2 = c1 ∧ m / 4 % 2 = c2 ∧
    m / 8 % 2 = c3 ∧ m / 16 % 2 = c4 ∧ m / 32 % 2 = c5 ∧
    m / 64 % 2 = c6 ∧ m / 128 % 2 = c7 ∧ m / 256 % 2 = c8 := by
  dsimp only
  omega

private lemma bipartite_three_three (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hA_ind : ∀ i j : Fin 6, i.val < 3 → j.val < 3 → ¬ G.Adj i j)
    (hB_ind : ∀ i j : Fin 6, 3 ≤ i.val → 3 ≤ j.val → ¬ G.Adj i j) :
    ∃ w : List (Fin 6), IsRepresentedBy G 2 w := by
  let b (i j : Fin 3) : ℕ :=
    if G.Adj ⟨i.val, by omega⟩ ⟨3 + j.val, by omega⟩ then 1 else 0
  have hb_le : ∀ i j : Fin 3, b i j ≤ 1 := fun i j => by dsimp only [b]; split_ifs <;> omega
  generalize hm_def :
    b 0 0 + 2 * (b 0 1 + 2 * (b 0 2 + 2 * (b 1 0 + 2 * (b 1 1 + 2 * (b 1 2 +
      2 * (b 2 0 + 2 * (b 2 1 + 2 * b 2 2))))))) = m
  have hbh := bit_horner (b 0 0) (b 0 1) (b 0 2) (b 1 0) (b 1 1) (b 1 2) (b 2 0) (b 2 1) (b 2 2)
    (hb_le 0 0) (hb_le 0 1) (hb_le 0 2) (hb_le 1 0) (hb_le 1 1) (hb_le 1 2)
    (hb_le 2 0) (hb_le 2 1) (hb_le 2 2)
  dsimp only at hbh
  rw [hm_def] at hbh
  have hm_lt : m < 512 := hbh.1
  have hbit : ∀ i j : Fin 3,
      ((m / 2 ^ (3 * i.val + j.val)) % 2 == 1) =
        decide (G.Adj ⟨i.val, by omega⟩ ⟨3 + j.val, by omega⟩) := by
    have hm00 : m / 2 ^ 0 % 2 = b 0 0 := hbh.2.1
    have hm01 : m / 2 ^ 1 % 2 = b 0 1 := hbh.2.2.1
    have hm02 : m / 2 ^ 2 % 2 = b 0 2 := hbh.2.2.2.1
    have hm10 : m / 2 ^ 3 % 2 = b 1 0 := hbh.2.2.2.2.1
    have hm11 : m / 2 ^ 4 % 2 = b 1 1 := hbh.2.2.2.2.2.1
    have hm12 : m / 2 ^ 5 % 2 = b 1 2 := hbh.2.2.2.2.2.2.1
    have hm20 : m / 2 ^ 6 % 2 = b 2 0 := hbh.2.2.2.2.2.2.2.1
    have hm21 : m / 2 ^ 7 % 2 = b 2 1 := hbh.2.2.2.2.2.2.2.2.1
    have hm22 : m / 2 ^ 8 % 2 = b 2 2 := hbh.2.2.2.2.2.2.2.2.2
    intro i j
    fin_cases i <;> fin_cases j
    · change (m / 2 ^ 0 % 2 == 1) = decide (G.Adj ⟨0, by decide⟩ ⟨3, by decide⟩)
      rw [hm00]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 1 % 2 == 1) = decide (G.Adj ⟨0, by decide⟩ ⟨4, by decide⟩)
      rw [hm01]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 2 % 2 == 1) = decide (G.Adj ⟨0, by decide⟩ ⟨5, by decide⟩)
      rw [hm02]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 3 % 2 == 1) = decide (G.Adj ⟨1, by decide⟩ ⟨3, by decide⟩)
      rw [hm10]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 4 % 2 == 1) = decide (G.Adj ⟨1, by decide⟩ ⟨4, by decide⟩)
      rw [hm11]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 5 % 2 == 1) = decide (G.Adj ⟨1, by decide⟩ ⟨5, by decide⟩)
      rw [hm12]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 6 % 2 == 1) = decide (G.Adj ⟨2, by decide⟩ ⟨3, by decide⟩)
      rw [hm20]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 7 % 2 == 1) = decide (G.Adj ⟨2, by decide⟩ ⟨4, by decide⟩)
      rw [hm21]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
    · change (m / 2 ^ 8 % 2 == 1) = decide (G.Adj ⟨2, by decide⟩ ⟨5, by decide⟩)
      rw [hm22]; dsimp only [b]; split_ifs with h <;> (simp; exact h)
  have hmask_adj : ∀ a b' : Fin 6, maskAdj m a b' = decide (G.Adj a b') := by
    intro a b'
    unfold maskAdj
    by_cases h1 : a.val < 3 ∧ 3 ≤ b'.val
    · rw [if_pos h1]
      have hb := hbit ⟨a.val, h1.1⟩ ⟨b'.val - 3, by omega⟩
      have heqa : (⟨a.val, by omega⟩ : Fin 6) = a := Fin.ext rfl
      have heqb : (⟨3 + (b'.val - 3), by omega⟩ : Fin 6) = b' :=
        Fin.ext (show 3 + (b'.val - 3) = b'.val by omega)
      have hb' : ((m / 2 ^ (3 * a.val + (b'.val - 3))) % 2 == 1) =
          decide (G.Adj ⟨a.val, by omega⟩ ⟨3 + (b'.val - 3), by omega⟩) := hb
      rw [hb', heqa, heqb]
    · rw [if_neg h1]
      by_cases h2 : b'.val < 3 ∧ 3 ≤ a.val
      · rw [if_pos h2]
        have hb := hbit ⟨b'.val, h2.1⟩ ⟨a.val - 3, by omega⟩
        have heqb : (⟨b'.val, by omega⟩ : Fin 6) = b' := Fin.ext rfl
        have heqa : (⟨3 + (a.val - 3), by omega⟩ : Fin 6) = a :=
          Fin.ext (show 3 + (a.val - 3) = a.val by omega)
        have hb' : ((m / 2 ^ (3 * b'.val + (a.val - 3))) % 2 == 1) =
            decide (G.Adj ⟨b'.val, by omega⟩ ⟨3 + (a.val - 3), by omega⟩) := hb
        rw [hb', heqb, heqa]
        by_cases hadj : G.Adj a b'
        · simp [hadj, hadj.symm]
        · have hns : ¬ G.Adj b' a := fun h => hadj h.symm
          simp [hadj, hns]
      · rw [if_neg h2]
        symm
        rw [decide_eq_false_iff_not]
        by_cases ha : a.val < 3
        · exact hA_ind a b' ha (by omega)
        · exact hB_ind a b' (by omega) (by omega)
  have hchk := checkMask_all m hm_lt
  unfold checkMask at hchk
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq, Bool.or_eq_true] at hchk
  refine ⟨decodeWord (wordLookup m), hchk.1, ?_⟩
  intro a b' hab
  rcases hchk.2 a b' with rfl | hpair
  · exact absurd rfl hab
  · rw [hmask_adj a b'] at hpair
    unfold Alternate
    rw [← isChainNe_iff, ← hpair]
    simp

end OMA.Proof_wp_bipartite_graph_R1_H1

theorem OMA.solution : OMA.R_wp_bipartite_graph_R1.H1 := by
  classical
  intro V _ _ G hcard hcol
  obtain ⟨c⟩ := hcol
  let C0 : Finset V := Finset.univ.filter (fun v => c v = 0)
  let C1 : Finset V := Finset.univ.filter (fun v => c v = 1)
  have hdisj01 : Disjoint C0 C1 := by
    rw [Finset.disjoint_left]
    intro v h0 h1
    have e0 := (Finset.mem_filter.mp h0).2
    have e1 := (Finset.mem_filter.mp h1).2
    rw [e0] at e1
    exact absurd e1 (by decide)
  have hcov01 : C0 ∪ C1 = Finset.univ := by
    ext v
    simp only [C0, C1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hlt := (c v).isLt
    have h01 : (c v).val = 0 ∨ (c v).val = 1 := by omega
    rcases h01 with h0 | h1
    · left; exact Fin.ext h0
    · right; exact Fin.ext h1
  have hC0_ind : ∀ u ∈ C0, ∀ v ∈ C0, ¬ G.Adj u v := by
    intro u hu v hv hadj
    have e0 := (Finset.mem_filter.mp hu).2
    have e1 := (Finset.mem_filter.mp hv).2
    exact c.valid hadj (e0.trans e1.symm)
  have hC1_ind : ∀ u ∈ C1, ∀ v ∈ C1, ¬ G.Adj u v := by
    intro u hu v hv hadj
    have e0 := (Finset.mem_filter.mp hu).2
    have e1 := (Finset.mem_filter.mp hv).2
    exact c.valid hadj (e0.trans e1.symm)
  have hsum : C0.card + C1.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj01, hcov01, Finset.card_univ]
  by_cases h0le : C0.card ≤ 2
  · exact OMA.Proof_wp_bipartite_graph_R1_H1.bipartite_le_two G C0 C1 hdisj01 hcov01
      hC0_ind hC1_ind h0le
  · by_cases h1le : C1.card ≤ 2
    · exact OMA.Proof_wp_bipartite_graph_R1_H1.bipartite_le_two G C1 C0 hdisj01.symm
        (Finset.union_comm C0 C1 ▸ hcov01) hC1_ind hC0_ind h1le
    · have h0eq : C0.card = 3 := by omega
      have h1eq : C1.card = 3 := by omega
      let e0 : C0 ≃ Fin 3 := (Fintype.equivFinOfCardEq (by simpa using h0eq))
      let e1 : C1 ≃ Fin 3 := (Fintype.equivFinOfCardEq (by simpa using h1eq))
      let eSum : V ≃ (C0 ⊕ C1) :=
        { toFun := fun v => if hv : v ∈ C0 then Sum.inl ⟨v, hv⟩
            else Sum.inr ⟨v, (Finset.mem_union.mp (hcov01 ▸ Finset.mem_univ v)).resolve_left hv⟩,
          invFun := fun s => Sum.elim Subtype.val Subtype.val s,
          left_inv := fun v => by by_cases hv : v ∈ C0 <;> simp [hv],
          right_inv := by
            rintro (⟨v, hv⟩ | ⟨v, hv⟩)
            · simp [hv]
            · have hv0 : v ∉ C0 := Finset.disjoint_right.mp hdisj01 hv
              simp [hv0] }
      let eFin : (Fin 3 ⊕ Fin 3) ≃ Fin 6 :=
        { toFun := fun s => Sum.elim (fun i => ⟨i.val, by omega⟩) (fun j => ⟨3 + j.val, by omega⟩) s,
          invFun := fun k => if hk : k.val < 3 then Sum.inl ⟨k.val, hk⟩
            else Sum.inr ⟨k.val - 3, by omega⟩,
          left_inv := by
            rintro (i | j)
            · simp [i.isLt]
            · simp only [Sum.elim_inr, show ¬ (3 + j.val < 3) by omega, ↓reduceDIte]
              congr 1; exact Fin.ext (show 3 + j.val - 3 = j.val by omega),
          right_inv := fun k => by
            by_cases hk : k.val < 3
            · simp [hk]
            · simp only [hk, ↓reduceDIte, Sum.elim_inr]
              exact Fin.ext (show 3 + (k.val - 3) = k.val by omega) }
      let e : V ≃ Fin 6 := eSum.trans ((Equiv.sumCongr e0 e1).trans eFin)
      let H : SimpleGraph (Fin 6) := G.comap e.symm
      have he_symm_lt : ∀ i : Fin 6, i.val < 3 → e.symm i ∈ C0 := by
        intro i hi
        change eSum.symm ((Equiv.sumCongr e0 e1).symm (eFin.symm i)) ∈ C0
        have h1 : eFin.symm i = Sum.inl ⟨i.val, hi⟩ := by simp [eFin, hi]
        rw [h1]
        exact (e0.symm ⟨i.val, hi⟩).property
      have he_symm_ge : ∀ i : Fin 6, 3 ≤ i.val → e.symm i ∈ C1 := by
        intro i hi
        change eSum.symm ((Equiv.sumCongr e0 e1).symm (eFin.symm i)) ∈ C1
        have h1 : eFin.symm i = Sum.inr ⟨i.val - 3, by omega⟩ := by
          simp [eFin, show ¬ i.val < 3 by omega]
        rw [h1]
        exact (e1.symm ⟨i.val - 3, by omega⟩).property
      have hH_A : ∀ i j : Fin 6, i.val < 3 → j.val < 3 → ¬ H.Adj i j :=
        fun i j hi hj => hC0_ind _ (he_symm_lt i hi) _ (he_symm_lt j hj)
      have hH_B : ∀ i j : Fin 6, 3 ≤ i.val → 3 ≤ j.val → ¬ H.Adj i j :=
        fun i j hi hj => hC1_ind _ (he_symm_ge i hi) _ (he_symm_ge j hj)
      obtain ⟨w, hw⟩ := OMA.Proof_wp_bipartite_graph_R1_H1.bipartite_three_three H hH_A hH_B
      refine ⟨w.map e.symm, OMA.Proof_wp_bipartite_graph_R1_H1.isRepresentedBy_transport e ?_ hw⟩
      intro u v
      simp [H]
