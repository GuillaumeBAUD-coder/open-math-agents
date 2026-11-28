import OMAStatements.S_mo_275692

open Equiv Finset

namespace OMA.Mo275692

open OMA.S_mo_275692

private abbrev left {n : ℕ} (j : Fin n) := j.castSucc
private abbrev right {n : ℕ} (j : Fin n) := j.succ
private abbrev transposition {n : ℕ} (j : Fin n) := Equiv.swap (left j) (right j)

private theorem adjacent_lt {n : ℕ} (j : Fin n) : left j < right j := by
  change j.val < j.val + 1
  omega

private theorem step_left {n : ℕ} (p : G n) (j : Fin n) : step p j (left j) = p (right j) := by
  simp [step]

private theorem step_right {n : ℕ} (p : G n) (j : Fin n) : step p j (right j) = p (left j) := by
  simp [step]

private theorem step_other {n : ℕ} (p : G n) (j : Fin n) (i : Fin (n + 1))
    (hl : i ≠ left j) (hr : i ≠ right j) : step p j i = p i := by
  simp [step, swap_apply_of_ne_of_ne hl hr]

private theorem step_twice {n : ℕ} (p : G n) (j : Fin n) : step (step p j) j = p := by
  ext i
  simp [step]

private def PSet {n : ℕ} (p : G n) (t : Fin (n+1)) (m : ℕ) : Finset (Fin (n+1)) :=
  univ.filter fun i ↦ i.val < m ∧ t < p i

private def prefixCount {n : ℕ} (p : G n) (t : Fin (n+1)) (m : ℕ) : ℕ := (PSet p t m).card

private def bit {n : ℕ} (t x : Fin (n+1)) : ℕ := if t < x then 1 else 0

private theorem pref_succ {n : ℕ} (p : G n) (t i : Fin (n+1)) :
    prefixCount p t (i.val + 1) = prefixCount p t i.val + bit t (p i) := by
  classical
  unfold prefixCount bit
  by_cases hi : t < p i
  · have he : PSet p t (i.val+1) = insert i (PSet p t i.val) := by
      ext j
      simp only [PSet, mem_filter, mem_univ, true_and, mem_insert]
      rcases eq_or_ne j i with rfl | hj
      · simp [hi]
      · have hne : j.val ≠ i.val := fun h ↦ hj (Fin.ext h)
        simp only [hj, false_or]
        omega
    have hnot : i ∉ PSet p t i.val := by simp [PSet]
    rw [he, card_insert_of_notMem hnot, if_pos hi]
  · have he : PSet p t (i.val+1) = PSet p t i.val := by
      ext j
      simp only [PSet, mem_filter, mem_univ, true_and]
      rcases eq_or_ne j i with rfl | hj
      · simp [hi]
      · have hne : j.val ≠ i.val := fun h ↦ hj (Fin.ext h)
        omega
    rw [he, if_neg hi, add_zero]

private theorem prefix_step_same {n : ℕ} (p : G n) (t : Fin (n+1)) (j : Fin n)
    (m : ℕ) (hm : m ≠ j.val+1) : prefixCount (step p j) t m = prefixCount p t m := by
  classical
  unfold prefixCount
  apply card_equiv (transposition j)
  intro i
  simp only [PSet, mem_filter, mem_univ, true_and]
  change (i.val < m ∧ t < p (transposition j i)) ↔
    ((transposition j i).val < m ∧ t < p (transposition j i))
  have h : (transposition j i).val < m ↔ i.val < m := by
    rcases eq_or_ne i (left j) with rfl | hl
    · rw [show transposition j (left j) = right j from swap_apply_left _ _]
      change j.val+1 < m ↔ j.val < m
      omega
    rcases eq_or_ne i (right j) with rfl | hr
    · rw [show transposition j (right j) = left j from swap_apply_right _ _]
      change j.val < m ↔ j.val+1 < m
      omega
    rw [show transposition j i = i from swap_apply_of_ne_of_ne hl hr]
  rw [h]

private abbrev descend {n : ℕ} (p : G n) (j : Fin n) : Prop := p (right j) < p (left j)

private theorem prefix_greedy {n : ℕ} (p : G n) (t : Fin (n+1)) (j : Fin n) :
    prefixCount (if descend p j then step p j else p) t (j.val+1) =
      max (prefixCount p t j.val) (prefixCount p t (j.val+2)-1) := by
  classical
  have hL := pref_succ p t (left j)
  have hR := pref_succ p t (right j)
  change prefixCount p t (j.val+1) = prefixCount p t j.val + bit t (p (left j)) at hL
  change prefixCount p t (j.val+2) = _ at hR
  change _ = prefixCount p t (j.val+1) + bit t (p (right j)) at hR
  have hstep : prefixCount (step p j) t (j.val+1) = prefixCount p t j.val + bit t (p (right j)) := by
    have h := pref_succ (step p j) t (left j)
    change prefixCount (step p j) t (j.val+1) = prefixCount (step p j) t j.val +
      bit t (step p j (left j)) at h
    rw [prefix_step_same p t j j.val (by omega), step_left] at h
    exact h
  by_cases hj : descend p j
  · rw [if_pos hj, hstep, hR, hL]
    change p (right j) < p (left j) at hj
    by_cases h₁ : t < p (left j) <;> by_cases h₂ : t < p (right j) <;>
      simp only [bit, h₁, h₂, if_true, if_false] <;> omega
  · rw [if_neg hj, hR, hL]
    change ¬ p (right j) < p (left j) at hj
    by_cases h₁ : t < p (left j) <;> by_cases h₂ : t < p (right j) <;>
      simp only [bit, h₁, h₂, if_true, if_false] <;> omega

private def dominated {n : ℕ} (p q : G n) : Prop := ∀ t m, prefixCount p t m ≤ prefixCount q t m

private theorem greedy_dominated {n : ℕ} (p q : G n) (j : Fin n) (h : dominated p q) :
    dominated (if descend p j then step p j else p) (step q j) := by
  classical
  intro t m
  by_cases hm : m = j.val+1
  · subst m
    rw [prefix_greedy]
    have hL := pref_succ (step q j) t (left j)
    have hR := pref_succ (step q j) t (right j)
    change prefixCount (step q j) t (j.val+1) = prefixCount (step q j) t j.val + _ at hL
    change prefixCount (step q j) t (j.val+2) =
      prefixCount (step q j) t (j.val+1) + _ at hR
    rw [prefix_step_same _ _ _ j.val (by omega)] at hL
    rw [prefix_step_same _ _ _ (j.val+2) (by omega)] at hR
    have hr : bit t (step q j (right j)) ≤ 1 := by unfold bit; split <;> omega
    have hl := h t j.val
    have hu := h t (j.val+2)
    omega
  · rw [prefix_step_same _ _ _ _ hm]
    by_cases hj : descend p j
    · rw [if_pos hj, prefix_step_same _ _ _ _ hm]
      exact h t m
    · rw [if_neg hj]
      exact h t m

private theorem card_before {n m : ℕ} :
    ((univ : Finset (Fin (n+1))).filter fun i ↦ i.val < m).card = min m (n+1) := by
  rw [← card_range (min m (n+1))]
  let b := min m (n+1)
  apply card_bij (fun i _ ↦ i.val)
  · intro i hi
    rw [mem_range, lt_min_iff]
    exact ⟨(mem_filter.mp hi).2, i.isLt⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro k hk
    have hh := lt_min_iff.mp (mem_range.mp hk)
    exact ⟨⟨k, hh.2⟩, mem_filter.mpr ⟨mem_univ _, hh.1⟩, rfl⟩

private theorem prefix_rev {n : ℕ} (t : Fin (n+1)) (m : ℕ) :
    prefixCount Fin.revPerm t m = min m (n - t.val) := by
  unfold prefixCount
  have hm : PSet Fin.revPerm t m =
      univ.filter (fun i : Fin (n+1) ↦ i.val < min m (n-t.val)) := by
    ext i
    simp only [PSet, mem_filter, mem_univ, true_and, lt_min_iff]
    change (_ ∧ t.val < n+1-(i.val+1)) ↔ _
    omega
  rw [hm, card_before]
  omega

private theorem dominated_rev {n : ℕ} (p : G n) : dominated p Fin.revPerm := by
  intro t m
  rw [prefix_rev]
  apply le_min
  · unfold prefixCount
    exact (card_le_card (s := PSet p t m)
      (t := (univ : Finset (Fin (n+1))).filter fun i ↦ i.val < m)
      (by
        intro i hi
        simp only [PSet, mem_filter, mem_univ, true_and] at hi ⊢
        exact hi.1)).trans (by rw [card_before]; exact min_le_left _ _)
  · have hs : ((univ : Finset (Fin (n+1))).filter fun i ↦ t < p i).card = n - t.val := by
      calc
        _ = ((univ : Finset (Fin (n+1))).filter fun i ↦ i.val < n - t.val).card := by
          apply card_equiv (p.trans Fin.revPerm)
          intro i
          simp only [mem_filter, mem_univ, true_and]
          change t.val < (p i).val ↔ n+1-((p i).val+1) < n-t.val
          omega
        _ = _ := by rw [card_before]; omega
    rw [← hs]
    apply card_le_card
    intro i hi
    simp only [PSet, mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2

private theorem eq_refl_of_pointwise_le {n : ℕ} {p : G n} (h : ∀ i, p i ≤ i) :
    p = Equiv.refl _ := by
  ext i
  by_contra! hn
  have hi : (p i).val < i.val := lt_of_le_of_ne (h i) hn
  have hlt := Finset.sum_lt_sum (s := (univ : Finset (Fin (n+1))))
    (f := fun j ↦ (p j).val) (g := Fin.val) (fun j _ ↦ h j) ⟨i, mem_univ _, hi⟩
  have he := Equiv.sum_comp p Fin.val
  exact hlt.ne he

private theorem dominated_id {n : ℕ} {p : G n} (h : dominated p (Equiv.refl _)) :
    p = Equiv.refl _ := by
  apply eq_refl_of_pointwise_le
  intro i
  by_contra! hi
  have hpos : 0 < prefixCount p i (i.val+1) := card_pos.mpr
    ⟨i, mem_filter.mpr ⟨mem_univ _, Nat.lt_succ_self _, hi⟩⟩
  have hzero : prefixCount (Equiv.refl _) i (i.val+1) = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro j hj
    have h' := (mem_filter.mp hj).2
    change j.val < i.val+1 ∧ i.val < j.val at h'
    omega
  have h' := h i (i.val+1)
  omega

private def inversions {n : ℕ} (p : G n) : Finset (Fin (n+1) × Fin (n+1)) :=
  univ.filter fun x ↦ x.1 < x.2 ∧ p.symm x.2 < p.symm x.1

private theorem inv_id (n : ℕ) : (inversions (Equiv.refl (Fin (n+1)))).card = 0 := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro p hp
  have h := (mem_filter.mp hp).2
  exact lt_asymm h.1 h.2

private theorem inv_rev (n : ℕ) :
    (inversions (@Fin.revPerm (n+1))).card = (n+1).choose 2 := by
  have h := card_product_filter_lt (s := (univ : Finset (Fin (n+1))))
  simpa [inversions, Fin.revPerm_symm, Fin.rev_lt_rev] using h

private theorem swap_lt_iff {n : ℕ} (j : Fin n) (a b : Fin (n+1)) :
    transposition j a < transposition j b ↔
      (a < b ∧ ¬ (a = left j ∧ b = right j)) ∨ (a = right j ∧ b = left j) := by
  have hne := (adjacent_lt j).ne
  rcases eq_or_ne a (left j) with rfl | hal
  · rcases eq_or_ne b (left j) with rfl | hbl
    · simp [hne]
    rcases eq_or_ne b (right j) with rfl | hbr
    · simp [hne, hne.symm, (adjacent_lt j).not_gt]
    simp only [swap_apply_left, swap_apply_of_ne_of_ne hbl hbr, hbr, hne,
      false_and, and_false, not_false_eq_true, and_true, or_false]
    have h₀ : b.val ≠ j.val := fun h ↦ hbl (Fin.ext h)
    have h₁ : b.val ≠ j.val+1 := fun h ↦ hbr (Fin.ext h)
    change j.val+1 < b.val ↔ j.val < b.val
    omega
  rcases eq_or_ne a (right j) with rfl | har
  · rcases eq_or_ne b (left j) with rfl | hbl
    · simp [hne]
    rcases eq_or_ne b (right j) with rfl | hbr
    · simp [hne.symm]
    simp only [swap_apply_right, swap_apply_of_ne_of_ne hbl hbr, hbl, hne.symm,
      false_and, and_false, not_false_eq_true, and_true, or_false]
    have h₁ : b.val ≠ j.val+1 := fun h ↦ hbr (Fin.ext h)
    change j.val < b.val ↔ j.val+1 < b.val
    omega
  rcases eq_or_ne b (left j) with rfl | hbl
  · simp only [swap_apply_left, swap_apply_of_ne_of_ne hal har, hal, har, false_and,
      not_false_eq_true, and_true, or_false]
    have h₀ : a.val ≠ j.val := fun h ↦ hal (Fin.ext h)
    change a.val < j.val+1 ↔ a.val < j.val
    omega
  rcases eq_or_ne b (right j) with rfl | hbr
  · simp only [swap_apply_right, swap_apply_of_ne_of_ne hal har, hal, har, false_and,
      not_false_eq_true, and_true, or_false]
    have h₀ : a.val ≠ j.val := fun h ↦ hal (Fin.ext h)
    change a.val < j.val ↔ a.val < j.val+1
    omega
  simp [swap_apply_of_ne_of_ne hal har, swap_apply_of_ne_of_ne hbl hbr, hal, har]

private theorem inv_step {n : ℕ} (p : G n) (j : Fin n) (hj : descend p j) :
    (inversions (step p j)).card + 1 = (inversions p).card := by
  classical
  let v := (p (right j), p (left j))
  have hv : v ∈ inversions p := by
    simp [inversions, v, hj]
  have he : inversions (step p j) = (inversions p).erase v := by
    ext x
    obtain ⟨a, b⟩ := x
    simp only [inversions, mem_filter, mem_univ, true_and, mem_erase]
    change (a < b ∧ transposition j (p.symm b) < transposition j (p.symm a)) ↔
      (a, b) ≠ v ∧ a < b ∧ p.symm b < p.symm a
    rw [swap_lt_iff]
    have han (z : _) (i : _) : p.symm z = i ↔ z = p i := by
      constructor
      · intro h
        simpa using congrArg p h
      · rintro rfl
        simp
    simp only [han, v]
    constructor
    · rintro ⟨hab, ⟨h, hn⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨fun h' ↦ hn ⟨congrArg Prod.snd h', congrArg Prod.fst h'⟩, hab, h⟩
      · exact (lt_asymm hj hab).elim
    · rintro ⟨hn, hab, h⟩
      exact ⟨hab, Or.inl ⟨h, fun q ↦ hn (Prod.ext q.2 q.1)⟩⟩
  rw [he, card_erase_of_mem hv]
  have := card_pos.mpr ⟨v, hv⟩
  omega

private theorem exists_sort {n : ℕ} (p : G n) : ∃ l, run p l = Equiv.refl _ := by
  by_cases h : ∃ j, descend p j
  · obtain ⟨j, hj⟩ := h
    obtain ⟨l, hl⟩ := exists_sort (step p j)
    exact ⟨j::l, hl⟩
  · have hm : Monotone p := Fin.monotone_iff_le_succ.mpr fun j ↦
      le_of_not_gt fun hj ↦ h ⟨j, hj⟩
    have hs : StrictMono p := hm.strictMono_of_injective p.injective
    have he : p = Equiv.refl _ := by
      apply eq_refl_of_pointwise_le
      intro i
      have hi := hs.id_le i
      have hsi : StrictMono p.symm := fun a b hab ↦
        (hs.lt_iff_lt).mp (by simpa using hab)
      simpa using hsi.id_le (p i)
    exact ⟨[], he⟩
termination_by (inversions p).card
decreasing_by have := inv_step p j hj; omega

private def prune {n : ℕ} (p : G n) : List (Fin n) → List (Fin n)
  | [] => []
  | j :: l => if descend p j then j :: prune (step p j) l else prune p l

private theorem prune_spec {n : ℕ} {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j)
    (p q : G n) (l : List (Fin n)) (hpq : dominated p q) :
    dominated (run p (prune p l)) (run q l) ∧ cost w (prune p l) ≤ cost w l ∧
      (inversions (run p (prune p l))).card + (prune p l).length = (inversions p).card := by
  induction l generalizing p q with
  | nil => simp [prune, run, cost, hpq]
  | cons j l ih =>
    have h := greedy_dominated p q j hpq
    by_cases hj : descend p j
    · rw [if_pos hj] at h
      obtain ⟨h₁, h₂, h₃⟩ := ih _ _ h
      simp only [prune, if_pos hj, run, cost, List.map_cons, List.sum_cons, List.length_cons]
      exact ⟨h₁, add_le_add_right h₂ _, by have := inv_step p j hj; omega⟩
    · rw [if_neg hj] at h
      obtain ⟨h₁, h₂, h₃⟩ := ih _ _ h
      simp only [prune, if_neg hj, run]
      refine ⟨h₁, h₂.trans ?_, h₃⟩
      change cost w l ≤ w j + cost w l
      linarith [hw j]

private theorem run_append {n : ℕ} (p : G n) (l m : List (Fin n)) :
    run p (l ++ m) = run (run p l) m := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih => exact ih (step p j)

private theorem run_reverse {n : ℕ} (p : G n) (l : List (Fin n)) :
    run (run p l) l.reverse = p := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih =>
    rw [List.reverse_cons, run_append]
    change run (run (run (step p j) l) l.reverse) [j] = p
    rw [ih]
    exact step_twice p j

private theorem cost_reverse {n : ℕ} (w : Fin n → ℝ) (l : List (Fin n)) :
    cost w l.reverse = cost w l := by
  simp [cost, List.map_reverse]

private theorem run_trans {n : ℕ} (p q : G n) (l : List (Fin n)) :
    run (p.trans q) l = (run p l).trans q := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih => exact ih (step p j)

private theorem finite_length_costs {n : ℕ} (w : Fin n → ℝ) (k : ℕ) :
    {x | ∃ l : List (Fin n), l.length = k ∧ cost w l = x}.Finite := by
  apply (Set.finite_range (fun f : Fin k → Fin n ↦ cost w (List.ofFn f))).subset
  rintro _ ⟨l, rfl, rfl⟩
  exact ⟨l.get, congrArg (cost w) (List.ofFn_get l)⟩

private theorem reduced_min {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∃ l : List (Fin n), l.length = (n+1).choose 2 ∧ run Fin.revPerm l = Equiv.refl _ ∧
      ∀ m, run Fin.revPerm m = Equiv.refl _ → cost w l ≤ cost w m := by
  classical
  let S := {x : ℝ | ∃ l : List (Fin n), l.length = (n+1).choose 2 ∧
    run Fin.revPerm l = Equiv.refl _ ∧ cost w l = x}
  have hprune (m : List (Fin n)) (hm : run Fin.revPerm m = Equiv.refl _) :
      cost w (prune Fin.revPerm m) ∈ S ∧ cost w (prune Fin.revPerm m) ≤ cost w m := by
    obtain ⟨hdom, hcost, hinv⟩ := prune_spec hw Fin.revPerm Fin.revPerm m
      (dominated_rev Fin.revPerm)
    rw [hm] at hdom
    have hrun := dominated_id hdom
    rw [hrun, inv_id, zero_add, inv_rev] at hinv
    exact ⟨⟨_, hinv, hrun, rfl⟩, hcost⟩
  obtain ⟨m, hm⟩ := exists_sort (@Fin.revPerm (n+1))
  have hfinite : S.Finite :=
    (finite_length_costs w ((n+1).choose 2)).subset fun _ ⟨l, h, _, hc⟩ ↦ ⟨l, h, hc⟩
  let s := hfinite.toFinset
  have hmem : ∀ x, x ∈ s ↔ x ∈ S := fun x ↦ hfinite.mem_toFinset
  have hne : s.Nonempty := ⟨_, (hmem _).2 (hprune m hm).1⟩
  obtain ⟨l, hl, hrun, hc⟩ := (hmem _).mp (min'_mem s hne)
  refine ⟨l, hl, hrun, fun m hm ↦ ?_⟩
  rw [hc]
  exact (min'_le s _ ((hmem _).2 (hprune m hm).1)).trans (hprune m hm).2

private theorem diameter_result (n : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (IsGreatest {d : ℝ | ∃ p q : G n, distance w p q = d}
        (distance w (Equiv.refl _) Fin.revPerm)) ∧
    ∃ l : List (Fin n), l.length = (n+1).choose 2 ∧ run (Equiv.refl _) l = Fin.revPerm ∧
      IsLeast (costs w (Equiv.refl _) Fin.revPerm) (cost w l) := by
  obtain ⟨l, hlen, hl, hmin⟩ := reduced_min w hw
  have hrev : run (Equiv.refl _) l.reverse = Fin.revPerm := hl ▸ run_reverse Fin.revPerm l
  have hleast : IsLeast (costs w (Equiv.refl _) Fin.revPerm) (cost w l.reverse) := by
    refine ⟨⟨l.reverse, hrev, rfl⟩, fun r ⟨m, hm, hc⟩ ↦ ?_⟩
    have hm' : run Fin.revPerm m.reverse = Equiv.refl _ := hm ▸ run_reverse (Equiv.refl _) m
    rw [← hc, cost_reverse, ← cost_reverse w m]
    exact hmin _ hm'
  have hdist : distance w (Equiv.refl _) Fin.revPerm = cost w l.reverse := hleast.csInf_eq
  refine ⟨⟨⟨_, _, rfl⟩, ?_⟩, ⟨l.reverse, by simpa using hlen, hrev, hleast⟩⟩
  rintro _ ⟨p, q, rfl⟩
  let r := q.trans p.symm
  let m := prune r l
  obtain ⟨hd, hc, _⟩ := prune_spec hw r Fin.revPerm l (dominated_rev r)
  rw [hl] at hd
  have hsort : run r m = Equiv.refl _ := dominated_id hd
  have hback : run (Equiv.refl _) m.reverse = r := hsort ▸ run_reverse r m
  have hpq : run p m.reverse = q := by
    calc
      _ = (run (Equiv.refl _) m.reverse).trans p := by
        simpa using run_trans (Equiv.refl _) p m.reverse
      _ = q := by
        rw [hback]
        ext i
        simp [r]
  have hb : BddBelow (costs w p q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, _, rfl⟩
    exact List.sum_nonneg fun x hx ↦ by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact hw j
  rw [hdist, cost_reverse]
  exact (csInf_le hb (show cost w m.reverse ∈ costs w p q from ⟨m.reverse, hpq, rfl⟩)).trans
    (by rw [cost_reverse]; exact hc)

private theorem example_distance :
    distance (![2, 1] : Fin 2 → ℝ) (Equiv.refl _) Fin.revPerm = 4 := by
  let w : Fin 2 → ℝ := ![2, 1]
  have hw (j : Fin 2) : 0 ≤ w j := by fin_cases j <;> norm_num [w]
  obtain ⟨l, hlen, hrun, hleast⟩ := (diameter_result 2 w hw).2
  change distance w (Equiv.refl _) Fin.revPerm = 4
  unfold distance
  rw [hleast.csInf_eq]
  apply le_antisymm
  · have h : run (Equiv.refl (Fin 3)) ([1, 0, 1] : List (Fin 2)) = Fin.revPerm := by decide
    apply hleast.2
    exact ⟨[1, 0, 1], h, by norm_num [cost, w]⟩
  · have hn : l.length = 3 := hlen
    obtain ⟨i, j, k, rfl⟩ : ∃ i j k, l = [i, j, k] := by
      cases l with
      | nil => simp at hn
      | cons i l => cases l with
        | nil => simp at hn
        | cons j l => cases l with
          | nil => simp at hn
          | cons k l =>
            have hl : l.length = 0 := by simpa using hn
            rw [List.length_eq_zero_iff.mp hl]
            exact ⟨i, j, k, rfl⟩
    let v : Fin 2 → ℕ := ![2, 1]
    have hv (i : Fin 2) : (v i : ℝ) = w i := by fin_cases i <;> norm_num [v, w]
    have h : ∀ i j k : Fin 2, run (Equiv.refl (Fin 3)) [i, j, k] = Fin.revPerm →
        4 ≤ v i + v j + v k := by decide
    have h' : (4 : ℝ) ≤ (v i : ℝ) + (v j : ℝ) + (v k : ℝ) := by
      exact_mod_cast h i j k hrun
    simpa [cost, hv, add_assoc] using h'

end OMA.Mo275692

theorem OMA.solution : type_of% @OMA.S_mo_275692.main :=
  ⟨OMA.Mo275692.diameter_result, OMA.Mo275692.example_distance⟩
