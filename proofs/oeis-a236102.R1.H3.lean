import OMAReductions.R_oeis_a236102_R1
import Mathlib

/-! The first thirteen partition counts. -/

namespace OMA.PartitionCounts

private def lists : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, n, _ => if n = 0 then [[]] else []
  | fuel+1, n, m =>
      if n = 0 then [[]] else
        (List.range (min n m)).flatMap fun a =>
          (lists fuel (n-(a+1)) (a+1)).map (fun tail => (a+1) :: tail)

private theorem lists_valid {fuel n m : ℕ} {l : List ℕ} (h : l ∈ lists fuel n m) :
    l.sum = n ∧ ∀ a ∈ l, 0 < a := by
  induction fuel generalizing n m l with
  | zero =>
      by_cases hn : n = 0
      · have hl : l = [] := by simpa [lists, hn] using h
        subst l
        simp [hn]
      · simp [lists, hn] at h
  | succ fuel ih =>
      by_cases hn : n = 0
      · have hl : l = [] := by simpa [lists, hn] using h
        subst l
        simp [hn]
      · simp only [lists, if_neg hn, List.mem_flatMap, List.mem_range, List.mem_map] at h
        obtain ⟨a, ha, tail, ht, rfl⟩ := h
        obtain ⟨hs, hp⟩ := ih ht
        have ha' : a < n := ha.trans_le (min_le_left _ _)
        refine ⟨by simp only [List.sum_cons]; omega, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · omega
        · exact hp b hb'

private theorem length_le_sum (l : List ℕ) (hp : ∀ a ∈ l, 0 < a) : l.length ≤ l.sum := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
      have h₁ := hp a (List.mem_cons_self)
      have h₂ := ih (fun b hb => hp b (List.mem_cons_of_mem _ hb))
      simp only [List.length_cons, List.sum_cons]
      omega

private theorem lists_complete (l : List ℕ) (m fuel : ℕ)
    (hpair : l.Pairwise (fun a b => b ≤ a))
    (hb : ∀ a ∈ l, a ≤ m) (hp : ∀ a ∈ l, 0 < a) (hfuel : l.length ≤ fuel) :
    l ∈ lists fuel l.sum m := by
  induction l generalizing m fuel with
  | nil =>
      cases fuel <;> simp [lists]
  | cons a tail ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have ha1 : 0 < a := hp a List.mem_cons_self
          have ha2 : a ≤ m := hb a List.mem_cons_self
          have hn : (a :: tail).sum ≠ 0 := by simp only [List.sum_cons]; omega
          have hsub : (a :: tail).sum - (a-1+1) = tail.sum := by
            simp only [List.sum_cons]
            omega
          have heq : a-1+1 = a := by omega
          obtain ⟨hbound,hpair'⟩ := List.pairwise_cons.mp hpair
          simp only [lists, if_neg hn, List.mem_flatMap, List.mem_range, List.mem_map]
          refine ⟨a-1, ?_, tail, ?_, by rw [heq]⟩
          · rw [lt_min_iff, List.sum_cons]
            omega
          · rw [hsub, heq]
            exact ih a fuel hpair' hbound
              (fun b h => hp b (List.mem_cons_of_mem _ h)) (by simpa using hfuel)

private def found (n : ℕ) : Finset (Multiset ℕ) :=
  List.toFinset (List.map (fun l : List ℕ => (l : Multiset ℕ)) (lists n n n))

private theorem mem_found (n : ℕ) (s : Multiset ℕ) :
    s ∈ found n ↔ ∃ l ∈ lists n n n, (l : Multiset ℕ) = s := by
  rw [found, List.mem_toFinset, List.mem_map]

private theorem count_eq (n : ℕ) : Fintype.card (Nat.Partition n) = (found n).card := by
  classical
  have h : ((Finset.univ : Finset (Nat.Partition n)).image Nat.Partition.parts) = found n := by
    ext s
    simp only [mem_found, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, rfl⟩
      let l := p.parts.sort (fun a b => b ≤ a)
      have hl : (l : Multiset ℕ) = p.parts := Multiset.sort_eq _ _
      have hs : l.sum = n := by
        change ((l : Multiset ℕ)).sum = n
        rw [hl, p.parts_sum]
      have hp : ∀ a ∈ l, 0 < a := by
        intro a ha
        apply p.parts_pos
        rw [← hl]
        exact ha
      have hb : ∀ a ∈ l, a ≤ n := by
        intro a ha
        apply p.le_of_mem_parts
        rw [← hl]
        exact ha
      have hlen : l.length ≤ n := (length_le_sum l hp).trans_eq hs
      have hm := lists_complete l n n (Multiset.pairwise_sort _ _) hb hp hlen
      exact ⟨l, by simpa only [hs] using hm, hl⟩
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨hs, hp⟩ := lists_valid hl
      exact ⟨⟨l, fun {a} ha => hp a ha, hs⟩, rfl⟩
  rw [← h, Finset.card_image_of_injective _ (fun _ _ heq => Nat.Partition.ext heq)]
  rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value0 : Fintype.card (Nat.Partition 0) = 1 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value1 : Fintype.card (Nat.Partition 1) = 1 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value2 : Fintype.card (Nat.Partition 2) = 2 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value3 : Fintype.card (Nat.Partition 3) = 3 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value4 : Fintype.card (Nat.Partition 4) = 5 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value5 : Fintype.card (Nat.Partition 5) = 7 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value6 : Fintype.card (Nat.Partition 6) = 11 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value7 : Fintype.card (Nat.Partition 7) = 15 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value8 : Fintype.card (Nat.Partition 8) = 22 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value9 : Fintype.card (Nat.Partition 9) = 30 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value10 : Fintype.card (Nat.Partition 10) = 42 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value11 : Fintype.card (Nat.Partition 11) = 56 := by
  rw [count_eq]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem value12 : Fintype.card (Nat.Partition 12) = 77 := by
  rw [count_eq]
  decide +kernel

end OMA.PartitionCounts

theorem OMA.solution : OMA.R_oeis_a236102_R1.H3 := by
  open OMA.PartitionCounts in
  exact ⟨value0, value1, value2, value3, value4, value5, value6, value7, value8, value9, value10, value11, value12⟩