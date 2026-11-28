import OMAStatements.S_oeis_a238873

-- Problem: A238873: Number of superdiagonal partitions: partitions (p1, p2, p3, ...) of n such that pi >= i.
-- Upstream: formal-conjectures statements/oeis-a238873.lean:0 (declaration OMA.S_oeis_a238873.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a238873 in
/-- A superdiagonal increasing listing gives a choice: take `z i = length - i`. -/
lemma OMA.aux_forward (y : List ℕ) (h : Superdiagonal y.reverse) : Choosable y := by
  refine ⟨fun i => y.length - i.val, ?_, ?_⟩
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    simp only at hij
    omega
  · intro i
    have hi := i.isLt
    have hlt : y.length - 1 - i.val < y.reverse.length := by
      rw [List.length_reverse]; omega
    have h1 := h ⟨y.length - 1 - i.val, hlt⟩
    simp only [List.get_eq_getElem, List.getElem_reverse] at h1
    have e : y.length - 1 - (y.length - 1 - i.val) = i.val := by omega
    simp only [e] at h1
    simp only [List.get_eq_getElem]
    constructor
    · omega
    · omega

open OMA.S_oeis_a238873 in
/-- A choice forces the increasing listing to be superdiagonal (pigeonhole). -/
lemma OMA.aux_backward (y : List ℕ) (hs : y.Pairwise (· ≥ ·)) (h : Choosable y) :
    Superdiagonal y.reverse := by
  obtain ⟨z, hz, hb⟩ := h
  intro i
  have hi : i.val < y.length := by
    have h0 := i.isLt
    have h1 : y.reverse.length = y.length := List.length_reverse
    omega
  simp only [List.get_eq_getElem, List.getElem_reverse]
  have hmlt : y.length - 1 - i.val < y.length := by omega
  have hcard : (Finset.univ : Finset (Fin (i.val + 1))).card
      ≤ (Finset.Icc 1 (y[y.length - 1 - i.val])).card := by
    apply Finset.card_le_card_of_injOn
      (fun k => z ⟨y.length - 1 - i.val + k.val, by have := k.isLt; omega⟩)
    · intro k _
      have hk := k.isLt
      have hb' := hb ⟨y.length - 1 - i.val + k.val, by omega⟩
      simp only [List.get_eq_getElem] at hb'
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hb'.1, hb'.2.trans ?_⟩
      rcases Nat.eq_zero_or_pos k.val with h0 | hpos
      · simp [h0]
      · exact List.pairwise_iff_getElem.mp hs (y.length - 1 - i.val)
          (y.length - 1 - i.val + k.val) hmlt (by omega) (by omega)
    · intro k1 _ k2 _ hkk
      have h2 := hz hkk
      have h3 := Fin.mk.inj h2
      apply Fin.ext
      omega
  simpa using hcard

theorem OMA.solution : type_of% @OMA.S_oeis_a238873.main := by
  intro n
  unfold OMA.S_oeis_a238873.a
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro p
  have hs : (OMA.S_oeis_a238873.parts n p).Pairwise (· ≥ ·) := by
    unfold OMA.S_oeis_a238873.parts
    exact Multiset.pairwise_sort _ _
  exact ⟨OMA.aux_forward _, OMA.aux_backward _ hs⟩
