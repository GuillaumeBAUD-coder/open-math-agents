import OMAStatements.S_oeis_a284937

namespace OMA.S_oeis_a284937





theorem iter_succ (k : ℕ) : iter (k + 1) = (iter k).flatMap sigma := by
  unfold iter
  rw [Function.iterate_succ_apply']

theorem len_flatMap (u : List ℕ) : 2 * u.length ≤ (u.flatMap sigma).length := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 2 ≤ (sigma x).length := by rcases x with _ | x <;> simp [sigma]
    omega

theorem len_iter (k : ℕ) : k + 1 ≤ (iter k).length := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter_succ]
    have := len_flatMap (iter k)
    omega

theorem iter_step (k : ℕ) : ∃ t, iter (k + 1) = iter k ++ t := by
  induction k with
  | zero => exact ⟨[1], by simp [iter, sigma]⟩
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

/-- Every iterate long enough to contain position i agrees with A284935 there. -/
theorem agree (K i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ (iter K).length) :
    A284935 i = (iter K).getD (i - 1) 0 := by
  unfold A284935
  rcases le_total i K with h | h
  · obtain ⟨t, ht⟩ := iter_mono h
    have := len_iter i
    rw [ht, List.getD_append _ _ _ _ (by omega)]
  · obtain ⟨t, ht⟩ := iter_mono h
    rw [ht, List.getD_append _ _ _ _ (by omega)]

/-- Both images have as many 1s as half their length, so the block of an image word ending at a
1 (position L, counted from 0) has 2 * (number of 1s) - (L + 1) in {0, 1, 2}: the block is an
image followed by nothing, by 1 or by 11. -/
theorem key (u : List ℕ) (L : ℕ) (hL : (u.flatMap sigma).getD L 0 = 1) :
    L + 1 ≤ 2 * ((u.flatMap sigma).take (L + 1)).count 1 ∧
      2 * ((u.flatMap sigma).take (L + 1)).count 1 ≤ L + 3 := by
  induction u generalizing L with
  | nil => simp at hL
  | cons x u ih =>
    rw [List.flatMap_cons] at hL ⊢
    rcases x with _ | x
    · simp only [sigma, List.cons_append, List.nil_append] at hL ⊢
      rcases L with _ | _ | L
      · simp at hL
      · simp
      · rw [List.getD_cons_succ, List.getD_cons_succ] at hL
        have := ih L hL
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp
        omega
    · simp only [sigma, List.cons_append, List.nil_append] at hL ⊢
      rcases L with _ | _ | _ | _ | L
      · simp
      · simp
      · simp at hL
      · simp at hL
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
          List.getD_cons_succ] at hL
        have := ih L hL
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp
        omega

theorem count_eq (K m : ℕ) (hm : m ≤ (iter K).length) :
    Nat.count (fun i => 1 ≤ i ∧ A284935 i = 1) (m + 1) = ((iter K).take m).count 1 := by
  induction m with
  | zero => simp [Nat.count_succ]
  | succ m ih =>
    have hlt : m < (iter K).length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hlt,
      Option.toList_some, List.count_append, List.count_singleton]
    have hag := agree K (m + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, List.getD_eq_getElem (iter K) 0 hlt] at hag
    by_cases h : (iter K)[m] = 1
    · simp [h, hag]
    · simp [h, hag]

theorem iter_last (k : ℕ) : ∃ t, iter k = t ++ [k % 2] := by
  induction k with
  | zero => exact ⟨[], by simp [iter]⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    rw [iter_succ, ht, List.flatMap_append]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : (k + 1) % 2 = 1 := by omega
      refine ⟨t.flatMap sigma ++ [0], ?_⟩
      rw [h, h']
      simp [sigma]
    · have h' : (k + 1) % 2 = 0 := by omega
      refine ⟨t.flatMap sigma ++ [1, 1, 0], ?_⟩
      rw [h, h']
      simp [sigma]

theorem infinite_ones : (Set.ofPred (fun i => 1 ≤ i ∧ A284935 i = 1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨t, ht⟩ := iter_last (2 * N + 1)
  have h2 : (2 * N + 1) % 2 = 1 := by omega
  rw [h2] at ht
  have hlen := len_iter (2 * N + 1)
  rw [ht, List.length_append, List.length_singleton] at hlen
  have hmem : t.length + 1 ∈ Set.ofPred (fun i => 1 ≤ i ∧ A284935 i = 1) := by
    show 1 ≤ t.length + 1 ∧ A284935 (t.length + 1) = 1
    refine ⟨by omega, ?_⟩
    rw [agree (2 * N + 1) (t.length + 1) (by omega) (by rw [ht]; simp), ht,
      Nat.add_sub_cancel, List.getD_append_right _ _ _ _ le_rfl]
    simp
  have := hN hmem
  omega

theorem conjecture : ∀ n : ℕ, 1 ≤ n → (2 * n : ℤ) - a n ∈ ({0, 1, 2} : Set ℤ) := by
  intro n hn
  have hinf := infinite_ones
  have hp : 1 ≤ a n ∧ A284935 (a n) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hc : Nat.count (fun i => 1 ≤ i ∧ A284935 i = 1) (a n) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  obtain ⟨m, hm⟩ : ∃ m, a n = m + 1 := ⟨a n - 1, by omega⟩
  rw [hm] at hp hc
  have hlen := len_iter (m + 1)
  have h1 := count_eq (m + 1) (m + 1) (by omega)
  rw [Nat.count_succ, hc, if_pos hp] at h1
  have hag := agree (m + 1) (m + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hag
  have hw : (iter (m + 1)).getD m 0 = 1 := by rw [← hag]; exact hp.2
  rw [iter_succ] at hw h1
  have hk := key (iter m) m hw
  rw [← h1] at hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hm]
  push_cast
  omega

/-- Control: a(n) at the position m + 1 of a 1 in the fourth iterate (54 letters). -/
theorem a_eq (k m : ℕ) (hm : m + 1 ≤ (iter 4).length)
    (h1 : ((iter 4).take m).count 1 + 1 = k) (h2 : (iter 4).getD m 0 = 1) : a k = m + 1 := by
  have hp : 1 ≤ m + 1 ∧ A284935 (m + 1) = 1 := by
    refine ⟨by omega, ?_⟩
    rw [agree 4 (m + 1) (by omega) hm, Nat.add_sub_cancel]
    exact h2
  have hc := count_eq 4 m (by omega)
  unfold a
  rw [← h1, Nat.add_sub_cancel, ← hc]
  exact Nat.nth_count hp

/-- Controls: a(1..8) = 2, 3, 4, 7, 8, 11, 12, 16, the entry's data. -/
example : a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 4 ∧ a 4 = 7 ∧ a 5 = 8 ∧ a 6 = 11 ∧ a 7 = 12 ∧ a 8 = 16 :=
  ⟨a_eq 1 1 (by decide) (by decide) (by decide), a_eq 2 2 (by decide) (by decide) (by decide),
    a_eq 3 3 (by decide) (by decide) (by decide), a_eq 4 6 (by decide) (by decide) (by decide),
    a_eq 5 7 (by decide) (by decide) (by decide), a_eq 6 10 (by decide) (by decide) (by decide),
    a_eq 7 11 (by decide) (by decide) (by decide),
    a_eq 8 15 (by decide) (by decide) (by decide)⟩

end OMA.S_oeis_a284937

theorem OMA.solution : type_of% @OMA.S_oeis_a284937.main :=
  OMA.S_oeis_a284937.conjecture
