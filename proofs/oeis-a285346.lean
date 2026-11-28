import OMAStatements.S_oeis_a285346

/-! Prefix agreement and the count comparison adapt the argument for A285343 in PR 22630. -/

namespace OMA.S_oeis_a285346

theorem iter_succ (k : ℕ) : iter (k + 1) = (iter k).flatMap sigma := by
  unfold iter
  rw [Function.iterate_succ_apply']

theorem len_flatMap (u : List ℕ) : u.length ≤ (u.flatMap sigma).length := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (sigma x).length := by rcases x with _ | x <;> simp [sigma]
    omega

theorem iter_step (k : ℕ) : ∃ t, iter (k + 1) = iter k ++ t := by
  induction k with
  | zero => exact ⟨[1, 0, 0], by rw [iter_succ]; rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap sigma, ?_⟩
    rw [iter_succ (k + 1), ht, List.flatMap_append, ← iter_succ, ht]

theorem iter_mono {j k : ℕ} (h : j ≤ k) : ∃ t, iter k = iter j ++ t := by
  induction k, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ k _ ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨s, hs⟩ := iter_step k
    exact ⟨t ++ s, by rw [hs, ht, List.append_assoc]⟩

theorem len_iter (k : ℕ) : k + 1 ≤ (iter k).length := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    obtain ⟨t, ht⟩ := iter_mono (Nat.zero_le k)
    have h0 : iter 0 = [1] := rfl
    rw [h0] at ht
    rw [iter_succ, ht, List.flatMap_append]
    rw [ht] at ih
    have h1 := len_flatMap t
    have h2 : ([1] : List ℕ).flatMap sigma = [1, 1, 0, 0] := rfl
    rw [h2, List.length_append]
    rw [List.length_append] at ih
    simp only [List.length_cons, List.length_nil] at ih ⊢
    omega

/-- Every iterate long enough to contain position i agrees with the word there. -/
theorem agree (K i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ (iter K).length) :
    A285345 i = (iter K).getD (i - 1) 0 := by
  unfold A285345
  rcases le_total i K with h | h
  · obtain ⟨t, ht⟩ := iter_mono h
    have := len_iter i
    rw [ht, List.getD_append _ _ _ _ (by omega)]
  · obtain ⟨t, ht⟩ := iter_mono h
    rw [ht, List.getD_append _ _ _ _ (by omega)]

theorem count_eq (K m : ℕ) (hm : m ≤ (iter K).length) :
    Nat.count (fun i => 1 ≤ i ∧ A285345 i = 0) (m + 1) = ((iter K).take m).count 0 := by
  induction m with
  | zero => simp [Nat.count_succ]
  | succ m ih =>
    have hlt : m < (iter K).length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hlt,
      Option.toList_some, List.count_append, List.count_singleton]
    have hag := agree K (m + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, List.getD_eq_getElem (iter K) 0 hlt] at hag
    by_cases h : (iter K)[m] = 0
    · simp [h, hag]
    · simp [h, hag]

/-- The zero with zero-based rank r has zero-based index 2r+1 or 2r+2.
Each complete block has length twice its number of zeros. -/
private theorem locate (u : List ℕ) (r : ℕ) (hr : r < u.length) :
    ∃ j, j < (u.flatMap sigma).length ∧ (u.flatMap sigma).getD j 0 = 0 ∧
      ((u.flatMap sigma).take j).count 0 = r ∧
      (j = 2*r+1 ∨ j = 2*r+2) := by
  induction u generalizing r with
  | nil => simp at hr
  | cons x u ih =>
    simp only [List.length_cons] at hr
    rw [List.flatMap_cons]
    cases x with
    | zero =>
      change ∃ j, j < (1 :: 0 :: u.flatMap sigma).length ∧ _
      cases r with
      | zero => exact ⟨1, by simp, rfl, rfl, Or.inl rfl⟩
      | succ r =>
        obtain ⟨j, hj, hz, hc, hb⟩ := ih r (by omega)
        refine ⟨j+2, by simp only [List.length_cons]; omega, hz, ?_, by omega⟩
        change (1 :: 0 :: (u.flatMap sigma).take j).count 0 = r + 1
        simp [hc]
    | succ x =>
      change ∃ j, j < (1 :: 1 :: 0 :: 0 :: u.flatMap sigma).length ∧ _
      rcases r with _ | _ | r
      · exact ⟨2, by simp, rfl, rfl, Or.inr rfl⟩
      · exact ⟨3, by simp, rfl, rfl, Or.inl rfl⟩
      · obtain ⟨j, hj, hz, hc, hb⟩ := ih r (by omega)
        refine ⟨j+4, by simp only [List.length_cons]; omega, hz, ?_, by omega⟩
        change (1 :: 1 :: 0 :: 0 :: (u.flatMap sigma).take j).count 0 = r+2
        simp [hc]

end OMA.S_oeis_a285346

open OMA.S_oeis_a285346 in
theorem OMA.solution : type_of% @OMA.S_oeis_a285346.main := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hr := len_iter r
  obtain ⟨j, hj, hz, hc, hb⟩ := locate (iter r) r (by omega)
  rw [← iter_succ] at hj hz hc
  have hp : 1 ≤ j + 1 ∧ A285345 (j + 1) = 0 :=
    ⟨by omega, by simpa [agree (r+1) (j+1) (by omega) (by omega)] using hz⟩
  have he : a (r+1) = j+1 := by
    unfold a
    rw [Nat.add_sub_cancel, ← hc, ← count_eq (r+1) j (by omega)]
    exact Nat.nth_count hp
  rw [he]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega
