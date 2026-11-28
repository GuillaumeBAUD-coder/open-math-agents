import OMAStatements.S_oeis_a285353
import Mathlib

namespace OMA.S_oeis_a285353

private theorem block_length (x : ℕ) : 2 ≤ (sigma x).length := by
  cases x <;> norm_num [sigma]

private theorem block_balance (x : ℕ) :
    2 * ((sigma x).count 0) = (sigma x).length := by
  cases x <;> rfl

private def mark : ℕ → List ℕ
  | 0 => [1]
  | _ + 1 => [0, 1]

private theorem mark_block_length (x : ℕ) : (mark x).length = (sigma x).count 0 := by
  cases x <;> rfl

private theorem mark_length (w : List ℕ) :
    (w.flatMap mark).length = (w.flatMap sigma).count 0 := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.count_append, mark_block_length, ih]

private theorem marked_block (x n : ℕ) (hn : n < (sigma x).count 0) :
    ∃ k, k < (sigma x).length ∧ (sigma x).getD k 0 = 0 ∧
      ((sigma x).take k).count 0 = n ∧
      2 * (n : ℤ) + 2 - k = ((mark x).getD n 0 : ℤ) := by
  cases x with
  | zero =>
    have hn0 : n = 0 := by
      have h : n < 1 := by simpa [sigma] using hn
      omega
    subst n
    exact ⟨1, by decide, by decide, by decide, by decide⟩
  | succ x =>
    have hn2 : n < 2 := by simpa [sigma] using hn
    interval_cases n
    · refine ⟨2, ?_, ?_, ?_, ?_⟩ <;> norm_num [sigma, mark]
    · refine ⟨3, ?_, ?_, ?_, ?_⟩ <;> norm_num [sigma, mark]

private theorem marked_location (w : List ℕ) (n : ℕ) (hn : n < (w.flatMap sigma).count 0) :
    ∃ k, k < (w.flatMap sigma).length ∧ (w.flatMap sigma).getD k 0 = 0 ∧
      ((w.flatMap sigma).take k).count 0 = n ∧
      2 * (n : ℤ) + 2 - k = ((w.flatMap mark).getD n 0 : ℤ) := by
  induction w generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    let u := sigma x
    let v := xs.flatMap sigma
    have hm := mark_block_length x
    change (mark x).length = u.count 0 at hm
    change n < (u ++ v).count 0 at hn
    rw [List.count_append] at hn
    change ∃ k, k < (u ++ v).length ∧ (u ++ v).getD k 0 = 0 ∧
      ((u ++ v).take k).count 0 = n ∧
      2 * (n : ℤ) + 2 - k = (((mark x) ++ xs.flatMap mark).getD n 0 : ℤ)
    by_cases head : n < u.count 0
    · obtain ⟨k, hk, hz, hc, he⟩ := marked_block x n head
      change k < u.length at hk
      refine ⟨k, by rw [List.length_append]; omega, ?_, ?_, ?_⟩
      · simpa only [List.getD_append _ _ _ _ hk] using hz
      · simpa [List.take_append, Nat.sub_eq_zero_of_le hk.le] using hc
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact he
    · obtain ⟨k, hk, hz, hc, he⟩ := ih (n - u.count 0) (by change _ < v.count 0; omega)
      have ub : 2 * u.count 0 = u.length := block_balance x
      have hs : u.length + k - u.length = k := by omega
      change k < v.length at hk
      refine ⟨u.length + k, by rw [List.length_append]; omega, ?_, ?_, ?_⟩
      · rw [List.getD_append_right _ _ _ _ (by omega), hs]
        exact hz
      · change (v.take k).count 0 = n - u.count 0 at hc
        rw [List.take_append, List.take_of_length_le (by omega), hs, List.count_append, hc]
        omega
      · rw [List.getD_append_right _ _ _ _ (by omega), hm, ← he]
        omega

private theorem expand_length (w : List ℕ) : 2 * w.length ≤ (w.flatMap sigma).length := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    have hx := block_length x
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

private theorem expand_balance (w : List ℕ) :
    2 * (w.flatMap sigma).count 0 = (w.flatMap sigma).length := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    have hx := block_balance x
    simp only [List.flatMap_cons, List.length_append, List.count_append]
    omega

private theorem iter_step (m : ℕ) : iter (m + 1) = (iter m).flatMap sigma := by
  simp only [iter, Function.iterate_succ_apply']

private theorem iter_length (m : ℕ) : m + 1 ≤ (iter m).length := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [iter_step]
    have h := expand_length (iter m)
    omega

private theorem iter_grows (m : ℕ) : iter m <+: iter (m + 1) := by
  induction m with
  | zero => exact ⟨[1,0,0], rfl⟩
  | succ m ih =>
    simpa only [← iter_step] using (ih.flatMap sigma)

private theorem iter_prefix (i j : ℕ) (h : i ≤ j) : iter i <+: iter j := by
  induction j, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ j h ih => exact ih.trans (iter_grows j)

private theorem digit_eq (m k : ℕ) (hk : k < (iter m).length) :
    A285345 (k + 1) = (iter m).getD k 0 := by
  unfold A285345
  rw [Nat.add_sub_cancel_right]
  by_cases h : k + 1 ≤ m
  · obtain ⟨tail, htail⟩ := iter_prefix (k + 1) m h
    rw [← htail, List.getD_append _ _ _ _ (by have := iter_length (k + 1); omega)]
  · obtain ⟨tail, htail⟩ := iter_prefix m (k + 1) (by omega)
    rw [← htail, List.getD_append _ _ _ _ hk]

private def zeroPosition (i : ℕ) : Prop := 1 ≤ i ∧ A285345 i = 0

private instance : DecidablePred zeroPosition := fun i => by unfold zeroPosition; infer_instance

private theorem count_eq (m k : ℕ) (hk : k ≤ (iter m).length) :
    Nat.count zeroPosition (k + 1) = ((iter m).take k).count 0 := by
  induction k with
  | zero => simp [Nat.count_succ, zeroPosition]
  | succ k ih =>
    have hlt : k < (iter m).length := by omega
    rw [Nat.count_succ, ih (by omega), ← List.take_concat_get' _ k hlt, List.count_append]
    have hd : A285345 (k + 1) = (iter m)[k] :=
      (digit_eq m k hlt).trans (List.getD_eq_getElem (iter m) 0 hlt)
    by_cases h : (iter m)[k] = 0 <;> simp [zeroPosition, hd, h]

private theorem marked_digit (m k : ℕ) (hk : k < ((iter m).flatMap mark).length) :
    A285351 (k + 1) = (((iter m).flatMap mark).getD k 0 : ℤ) := by
  rw [mark_length] at hk
  obtain ⟨j, hj, hz, hc, he⟩ := marked_location (iter m) k hk
  have hj' : j < (iter (m + 1)).length := by simpa only [iter_step] using hj
  have hzero : zeroPosition (j + 1) := by
    refine ⟨by omega, ?_⟩
    rw [digit_eq (m + 1) j hj', iter_step]
    exact hz
  have hcount : Nat.count zeroPosition (j + 1) = k := by
    rw [count_eq (m + 1) j hj'.le, iter_step]
    exact hc
  have hpos : A285346 (k + 1) = j + 1 := by
    change Nat.nth zeroPosition (k + 1 - 1) = j + 1
    rw [Nat.add_sub_cancel_right, ← hcount]
    exact Nat.nth_count hzero
  unfold A285351
  rw [hpos]
  omega

private def combined (x : ℕ) : List ℕ := (sigma x).flatMap mark

private theorem combined_balance (x : ℕ) :
    3 * (combined x).count 0 = (combined x).length := by
  cases x <;> rfl

private theorem combined_block_location (x n : ℕ) (hn : n < (combined x).count 0) :
    ∃ k, k < (combined x).length ∧ (combined x).getD k 0 = 0 ∧
      ((combined x).take k).count 0 = n ∧ 3 * n ≤ k + 1 ∧ k ≤ 3 * n := by
  cases x with
  | zero =>
    have hn0 : n = 0 := by
      have h : n < 1 := by simpa [combined, sigma, mark] using hn
      omega
    subst n
    exact ⟨0, by decide, by decide, by decide, by decide, by decide⟩
  | succ x =>
    have hn2 : n < 2 := by simpa [combined, sigma, mark] using hn
    interval_cases n
    · exact ⟨0, by norm_num [combined, sigma, mark], by norm_num [combined, sigma, mark], by norm_num [combined, sigma, mark], by decide, by decide⟩
    · exact ⟨2, by norm_num [combined, sigma, mark], by norm_num [combined, sigma, mark], by norm_num [combined, sigma, mark], by decide, by decide⟩

private theorem combined_location (w : List ℕ) (n : ℕ) (hn : n < (w.flatMap combined).count 0) :
    ∃ k, k < (w.flatMap combined).length ∧ (w.flatMap combined).getD k 0 = 0 ∧
      ((w.flatMap combined).take k).count 0 = n ∧ 3 * n ≤ k + 1 ∧ k ≤ 3 * n := by
  induction w generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    let u := combined x
    let v := xs.flatMap combined
    change n < (u ++ v).count 0 at hn
    rw [List.count_append] at hn
    change ∃ k, k < (u ++ v).length ∧ (u ++ v).getD k 0 = 0 ∧
      ((u ++ v).take k).count 0 = n ∧ 3 * n ≤ k + 1 ∧ k ≤ 3 * n
    by_cases head : n < u.count 0
    · obtain ⟨k, hk, hz, hc, hl, hu⟩ := combined_block_location x n head
      change k < u.length at hk
      refine ⟨k, by rw [List.length_append]; omega, ?_, ?_, hl, hu⟩
      · simpa only [List.getD_append _ _ _ _ hk] using hz
      · simpa [List.take_append, Nat.sub_eq_zero_of_le hk.le] using hc
    · obtain ⟨k, hk, hz, hc, hl, hu⟩ := ih (n - u.count 0) (by change _ < v.count 0; omega)
      have ub : 3 * u.count 0 = u.length := combined_balance x
      have hs : u.length + k - u.length = k := by omega
      change k < v.length at hk
      refine ⟨u.length + k, by rw [List.length_append]; omega, ?_, ?_, by omega, by omega⟩
      · rw [List.getD_append_right _ _ _ _ (by omega), hs]
        exact hz
      · change (v.take k).count 0 = n - u.count 0 at hc
        rw [List.take_append, List.take_of_length_le (by omega), hs, List.count_append, hc]
        omega

private theorem combined_count (w : List ℕ) :
    w.length ≤ (w.flatMap combined).count 0 := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    have hx : 1 ≤ (combined x).count 0 := by cases x <;> norm_num [combined, sigma, mark]
    simp only [List.length_cons, List.flatMap_cons, List.count_append]
    omega

private theorem derived_digit (m k : ℕ) (hk : k < ((iter m).flatMap combined).length) :
    A285351 (k + 1) = (((iter m).flatMap combined).getD k 0 : ℤ) := by
  have hp : (iter (m + 1)).flatMap mark = (iter m).flatMap combined := by
    rw [iter_step, List.flatMap_assoc]
    rfl
  rw [← hp]
  exact marked_digit (m + 1) k (by rw [hp]; exact hk)

private def derivedZero (i : ℕ) : Prop := 1 ≤ i ∧ A285351 i = 0

private noncomputable instance : DecidablePred derivedZero := Classical.decPred _

private theorem derived_count (m k : ℕ) (hk : k ≤ ((iter m).flatMap combined).length) :
    Nat.count derivedZero (k + 1) = (((iter m).flatMap combined).take k).count 0 := by
  induction k with
  | zero => simp [Nat.count_succ, derivedZero]
  | succ k ih =>
    have hlt : k < ((iter m).flatMap combined).length := by omega
    rw [Nat.count_succ, ih (by omega), ← List.take_concat_get' _ k hlt, List.count_append]
    have hd := derived_digit m k hlt
    rw [List.getD_eq_getElem _ _ hlt] at hd
    by_cases h : ((iter m).flatMap combined)[k] = 0 <;> simp [derivedZero, hd, h]

private theorem position_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, a n = k + 1 ∧ 3 * (n - 1) ≤ k + 1 ∧ k ≤ 3 * (n - 1) := by
  have hlength := iter_length n
  have hcount := combined_count (iter n)
  obtain ⟨k, hk, hz, hc, hl, hu⟩ := combined_location (iter n) (n - 1) (by omega)
  have hp : derivedZero (k + 1) := by
    refine ⟨by omega, ?_⟩
    rw [derived_digit n k hk, hz]
    exact Nat.cast_zero
  have hindex : Nat.count derivedZero (k + 1) = n - 1 :=
    (derived_count n k hk.le).trans hc
  refine ⟨k, ?_, hl, hu⟩
  change Nat.nth derivedZero (n - 1) = k + 1
  rw [← hindex]
  exact Nat.nth_count hp

end OMA.S_oeis_a285353

open OMA.S_oeis_a285353 in
theorem OMA.solution : type_of% @OMA.S_oeis_a285353.main := by
  intro n hn
  obtain ⟨k, hk, hl, hu⟩ := position_bound n hn
  rw [hk]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega