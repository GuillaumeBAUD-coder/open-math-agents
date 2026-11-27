import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Powerset

/-!
Count the deletion masks yielding a given trace of the alternating word with
an inserted one. Pascal's identity gives the count on an alternating run.
The append identity tracks the cut in the trace, so retaining the inserted
bit adds one product for each possible location of that bit.
-/

namespace Green92Counting

def traceCount : List Bool → List Bool → ℕ
  | [], w => if w = [] then 1 else 0
  | _ :: _, [] => 1
  | b :: source, c :: w => traceCount source (c :: w) +
      if b = c then traceCount source w else 0

def alternating : ℕ → Bool → List Bool
  | 0, _ => []
  | n + 1, b => b :: alternating n (!b)

def needed : Bool → List Bool → ℕ
  | _, [] => 0
  | b, c :: w => (if b = c then 1 else 2) + needed (!c) w

private theorem needed_le (b : Bool) (w : List Bool) : needed b w ≤ 2 * w.length := by
  induction w generalizing b with
  | nil => simp [needed]
  | cons c w ih =>
    have hh := ih (!c)
    by_cases h : b = c <;> simp [needed, h] <;> omega

theorem alternating_trace_count (n : ℕ) (b : Bool) (w : List Bool) :
    traceCount (alternating n b) w = ((n + 2 * w.length - needed b w) / 2).choose w.length := by
  induction n generalizing b w with
  | zero =>
    cases w with
    | nil => simp [traceCount, alternating]
    | cons c w =>
      have hneed : 0 < needed b (c :: w) := by
        unfold needed
        split <;> omega
      simp only [alternating, traceCount, List.cons_ne_nil, if_false, Nat.zero_add,
        List.length_cons] at hneed ⊢
      exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ n ih =>
    cases w with
    | nil => simp [alternating, traceCount]
    | cons c w =>
      simp only [alternating, traceCount, ih]
      by_cases h : b = c
      · subst c
        have hn := needed_le (!b) w
        have hb : (!b) ≠ b := by cases b <;> decide
        simp only [if_true, needed, hb, if_false, List.length_cons]
        let k := (n + 2 * w.length - needed (!b) w) / 2
        have htop : (n + 1 + 2 * (w.length + 1) - (1 + needed (!b) w)) / 2 = k + 1 := by
          dsimp [k]
          omega
        have hdrop : (n + 2 * (w.length + 1) - (2 + needed (!b) w)) / 2 = k := by
          dsimp [k]
          omega
        rw [htop, hdrop, Nat.choose_succ_succ']
        exact Nat.add_comm _ _
      · have hb : (!b) = c := by cases b <;> cases c <;> simp_all
        simp only [needed, h, hb, if_false, if_true, Nat.add_zero, List.length_cons]
        have he : (n + 2 * (w.length + 1) - (1 + needed (!c) w)) / 2 =
            (n + 1 + 2 * (w.length + 1) - (2 + needed (!c) w)) / 2 := by omega
        rw [he]

theorem needed_false_budget (w : List Bool) :
    2 * w.length - needed false w =
      2 * (w.zip w.tail).count (false, true) + if w.getLast? = some false then 1 else 0 := by
  induction w with
  | nil => simp [needed]
  | cons b w ih =>
    cases w with
    | nil => cases b <;> decide
    | cons c w =>
      have hb := needed_le false (c :: w)
      cases b <;> cases c <;> simp [needed] at ih hb ⊢ <;> omega

theorem alternating_even_trace_count (a : ℕ) (w : List Bool) :
    traceCount (alternating (2 * a) false) w =
      (a + (w.zip w.tail).count (false, true)).choose w.length := by
  rw [alternating_trace_count]
  have h := needed_false_budget w
  have hh := needed_le false w
  split at h <;> congr 2 <;> omega

@[simp] theorem traceCount_nil_right (u : List Bool) : traceCount u [] = 1 := by
  cases u <;> simp [traceCount]

theorem traceCount_append (u v w : List Bool) :
    traceCount (u ++ v) w =
      ∑ j ∈ Finset.range (w.length + 1), traceCount u (w.take j) * traceCount v (w.drop j) := by
  induction u generalizing w with
  | nil =>
    simp only [List.nil_append]
    symm
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hne
      cases w with
      | nil => simp at hj; omega
      | cons a w =>
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
        simp [traceCount]
    · simp
  | cons a u ih =>
    cases w with
    | nil => simp
    | cons b w =>
      let f (j : ℕ) := traceCount u ((b :: w).take j) * traceCount v ((b :: w).drop j)
      let g (j : ℕ) := traceCount u (w.take j) * traceCount v (w.drop j)
      change traceCount (a :: (u ++ v)) (b :: w) = _
      rw [traceCount, ih, ih]
      change (∑ j ∈ Finset.range (w.length + 1 + 1), f j) +
          (if a = b then ∑ j ∈ Finset.range (w.length + 1), g j else 0) = _
      rw [Finset.sum_range_succ', show (b :: w).length + 1 = w.length + 1 + 1 by rfl]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [f, g, List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons,
        traceCount_nil_right, Nat.one_mul]
      by_cases h : a = b
      · simp only [traceCount, h, if_true, Nat.add_mul, Finset.sum_add_distrib]
        omega
      · simp [traceCount, h]

theorem traceCount_defect (u v w : List Bool) :
    traceCount (u ++ true :: v) w = traceCount (u ++ v) w +
      ∑ j ∈ Finset.range w.length, if w[j]? = some true then
        traceCount u (w.take j) * traceCount v (w.drop (j + 1)) else 0 := by
  rw [traceCount_append, traceCount_append]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [List.drop_length, traceCount_nil_right, Nat.mul_one]
  have hsum :
      (∑ j ∈ Finset.range w.length, traceCount u (w.take j) * traceCount (true :: v) (w.drop j)) =
      (∑ j ∈ Finset.range w.length, traceCount u (w.take j) * traceCount v (w.drop j)) +
      ∑ j ∈ Finset.range w.length, if w[j]? = some true then
        traceCount u (w.take j) * traceCount v (w.drop (j + 1)) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have he : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hj'
    simp only [he, traceCount, Nat.mul_add, List.getElem?_eq_getElem hj', Option.some.injEq]
    by_cases h : true = w[j] <;> simp [h, eq_comm]
  rw [hsum]
  omega

theorem traceCount_eq_count_sublists (source w : List Bool) :
    traceCount source w = source.sublists'.count w := by
  induction source generalizing w with
  | nil => cases w <;> simp [traceCount]
  | cons b source ih =>
    rw [List.sublists'_cons, List.count_append]
    cases w with
    | nil =>
      rw [← ih, traceCount_nil_right, traceCount_nil_right]
      have h : ([] : List Bool) ∉ source.sublists'.map (List.cons b) := by simp
      rw [List.count_eq_zero_of_not_mem h, Nat.add_zero]
    | cons c w =>
      rw [traceCount, ih, ih]
      by_cases h : b = c
      · subst c
        rw [if_pos rfl, List.count_map_of_injective _ _ (fun _ _ h => (List.cons.inj h).2)]
      · have hn : c :: w ∉ source.sublists'.map (List.cons b) := by
          simp [List.mem_map, h]
        rw [if_neg h, List.count_eq_zero_of_not_mem hn]

private theorem recover_sublist {α : Type*} [DecidableEq α] {u v : List α}
    (h : List.Sublist u v) (hv : v.Nodup) : v.filter (fun i => decide (i ∈ u)) = u := by
  induction h with
  | slnil => rfl
  | @cons u v a h ih =>
    have ha : a ∉ u := fun hm => (List.nodup_cons.mp hv).1 (h.subset hm)
    simpa [ha] using ih hv.tail
  | @cons_cons u v a h ih =>
    have ht : v.filter (fun i => decide (i ∈ a :: u)) = v.filter (fun i => decide (i ∈ u)) := by
      apply List.filter_congr
      intro i hi
      have hne : i ≠ a := fun he => (List.nodup_cons.mp hv).1 (he ▸ hi)
      simp [hne]
    rw [List.filter_cons_of_pos (by simp), ht, ih hv.tail]

private def maskIndices {n : ℕ} (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun i => decide (i ∈ S)

private theorem maskIndices_injective (n : ℕ) : Function.Injective (@maskIndices n) := by
  intro S T h
  ext i
  simpa [maskIndices, List.mem_filter] using congrArg (fun l : List (Fin n) => i ∈ l) h

private theorem maskIndices_perm (n : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n))).toList.map maskIndices).Perm
      (List.finRange n).sublists' := by
  apply (List.perm_ext_iff_of_nodup
    (Finset.nodup_toList _ |>.map (maskIndices_injective n))
    (List.nodup_sublists'.mpr (List.nodup_finRange n))).mpr
  intro l
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, List.mem_sublists']
  constructor
  · rintro ⟨s, rfl⟩
    exact List.filter_sublist
  · intro hl
    refine ⟨l.toFinset, ?_⟩
    simpa [maskIndices] using recover_sublist hl (List.nodup_finRange n)

private theorem card_filter_eq_count_map {α : Type*} (S : Finset α) (f : α → List Bool)
    (w : List Bool) : (S.filter fun a => f a = w).card = (S.toList.map f).count w := by
  rw [List.count, List.countP_map]
  have he : ((fun x : List Bool => x == w) ∘ f) = fun a => decide (f a = w) := by
    funext a
    by_cases h : f a = w <;> simp [h, beq_eq_false_iff_ne]
  rw [he]
  change (S.filter fun a => f a = w).card =
    Multiset.countP (fun a => f a = w) (S.toList : Multiset α)
  rw [Finset.coe_toList, Multiset.countP_eq_card_filter, ← Finset.filter_val]
  rfl

theorem trace_mask_count {n : ℕ} (x : Fin n → Bool) (w : List Bool) :
    (Finset.univ.filter (fun S : Finset (Fin n) => (maskIndices S).map x = w)).card =
      traceCount (List.ofFn x) w := by
  rw [card_filter_eq_count_map, traceCount_eq_count_sublists, List.ofFn_eq_map, List.sublists'_map]
  simpa only [List.map_map, Function.comp_def] using
    ((maskIndices_perm n).map (List.map x)).count_eq w

@[simp] theorem length_alternating (n : ℕ) (b : Bool) : (alternating n b).length = n := by
  induction n generalizing b <;> simp [alternating, *]

private theorem getElem_alternating (n : ℕ) (b : Bool) (i : ℕ)
    (hi : i < (alternating n b).length) :
    (alternating n b)[i] = if i % 2 = 0 then b else !b := by
  induction n generalizing b i with
  | zero => simp at hi
  | succ n ih =>
    cases i with
    | zero => simp [alternating]
    | succ i =>
      simp only [alternating, List.getElem_cons_succ]
      rw [ih]
      by_cases h : i % 2 = 0
      · have h' : (i + 1) % 2 ≠ 0 := by omega
        simp [h, h']
      · have h' : (i + 1) % 2 = 0 := by omega
        simp [h, h']

theorem alternating_append_even (a c : ℕ) :
    alternating (2 * a) false ++ alternating (2 * c) false = alternating (2 * (a + c)) false := by
  induction a with
  | zero => simp [alternating]
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 2 by omega,
      show 2 * (a + 1 + c) = 2 * (a + c) + 2 by omega]
    simp [alternating, ih]

theorem defect_word {n a c : ℕ} (hn : n = 2 * a + 1 + 2 * c) :
    (List.ofFn fun i : Fin n => decide (i.val % 2 = if i.val < 2 * a then 1 else 0)) =
      alternating (2 * a) false ++ true :: alternating (2 * c) false := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons, length_alternating]
    omega
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn]
    by_cases hi : i < 2 * a
    · rw [List.getElem_append_left (by simpa using hi), getElem_alternating]
      change decide (i % 2 = if i < 2 * a then 1 else 0) = _
      by_cases he : i % 2 = 0
      · simp [hi, he]
      · have h' : i % 2 = 1 := by omega
        simp [hi, h']
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
      simp only [length_alternating]
      change decide (i % 2 = if i < 2 * a then 1 else 0) = _
      by_cases he : i = 2 * a
      · subst i
        simp [Nat.mul_mod_right]
      · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (show i - 2 * a ≠ 0 by omega)
        simp only [hj, List.getElem_cons_succ, getElem_alternating]
        by_cases hf : i % 2 = 0
        · have h' : j % 2 ≠ 0 := by omega
          simp [hi, hf, h']
        · have h' : j % 2 = 0 := by omega
          simp [hi, hf, h']

end Green92Counting

open Green92Counting in
theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1.H1 := by
  unfold OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1.H1
  intro n hn k W F B D b hb w
  have hn' : n = 2 * b + 1 + 2 * (2 * k + 1 - b) := by
    dsimp [k] at hb ⊢
    omega
  have hsum : b + (2 * k + 1 - b) = 2 * k + 1 := by omega
  change (Finset.univ.filter (fun S : Finset (Fin n) => (maskIndices S).map (W b) = w)).card = _
  rw [trace_mask_count, show List.ofFn (W b) = _ from defect_word hn',
    traceCount_defect, alternating_append_even, hsum]
  simp only [alternating_even_trace_count]
  rfl
