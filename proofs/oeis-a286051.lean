import OMAStatements.S_oeis_a286051

namespace OMA.S_oeis_a286051





/-! ### The Thue-Morse blocks -/

lemma tm_even (m : ℕ) : tm (2 * m) = tm m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · unfold tm
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp

lemma tm_odd (m : ℕ) : tm (2 * m + 1) = 1 - tm m := by
  unfold tm
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, List.count_cons_self]
  omega

lemma tm_le (n : ℕ) : tm n ≤ 1 := by
  unfold tm
  omega

/-! ### The scan -/

lemma pos_succ (k : ℕ) : pos (k + 1) =
    if tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 then pos k + 3
      else pos k + 1 := rfl

lemma pos_succ_of_even {k m : ℕ} (h : pos k = 2 * m) : pos (k + 1) = 2 * m + 1 := by
  rw [pos_succ, h, if_neg]
  rintro ⟨h1, h2, -⟩
  rw [tm_even] at h1
  rw [tm_odd, h1] at h2
  omega

lemma pos_even (j : ℕ) : ∃ m, pos (2 * j) = 2 * m := by
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨m, hm⟩ := ih
    have h1 := pos_succ_of_even hm
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e, pos_succ, h1]
    split_ifs
    · exact ⟨m + 2, by ring⟩
    · exact ⟨m + 1, by ring⟩

lemma w_pair (j : ℕ) :
    (w (2 * j) = 0 ∧ w (2 * j + 1) = 1) ∨ (w (2 * j) = 1 ∧ w (2 * j + 1) = 0) := by
  obtain ⟨m, hm⟩ := pos_even j
  have h1 := pos_succ_of_even hm
  unfold w
  rw [hm, h1, tm_even, tm_odd]
  have := tm_le m
  omega

/-! ### Counting the ones -/

lemma count_one (j : ℕ) : Nat.count (fun k => w k = 1) (2 * j) = j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e, Nat.count_succ, Nat.count_succ, ih]
    rcases w_pair j with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simp [h0, h1]
    · simp [h0, h1]

lemma nth_one (j : ℕ) :
    Nat.nth (fun k => w k = 1) j = 2 * j ∨ Nat.nth (fun k => w k = 1) j = 2 * j + 1 := by
  rcases w_pair j with ⟨h0, h1⟩ | ⟨h0, -⟩
  · right
    have := Nat.nth_count (p := fun k => w k = 1) h1
    rwa [Nat.count_succ, count_one, if_neg (by omega), add_zero] at this
  · left
    have := Nat.nth_count (p := fun k => w k = 1) h0
    rwa [count_one] at this

/-- Kimberling's conjecture: 2n - a(n) is 0 or 1 for every n >= 1. -/
theorem conjecture : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℤ) - a n = 0 ∨ 2 * (n : ℤ) - a n = 1) := by
  intro n hn
  unfold a
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rcases nth_one j with h | h
  · right
    rw [h]
    push_cast
    ring
  · left
    rw [h]
    push_cast
    ring

/-! ### Controls from the entries -/

/-- A286049 begins 0, 1, 1, 0, 0, 1, 0, 1 and A286051 begins 2, 3, 6, 8, as in the entries. -/
lemma controls : (List.range 8).map w = [0, 1, 1, 0, 0, 1, 0, 1] ∧
    a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 6 ∧ a 4 = 8 := by
  have hw : (List.range 8).map w = [0, 1, 1, 0, 0, 1, 0, 1] := by decide
  refine ⟨hw, ?_, ?_, ?_, ?_⟩
  · have h := Nat.nth_count (p := fun k => w k = 1) (n := 1) (by decide)
    have hc : Nat.count (fun k => w k = 1) 1 = 0 := by decide
    rw [hc] at h
    simp [a, h]
  · have h := Nat.nth_count (p := fun k => w k = 1) (n := 2) (by decide)
    have hc : Nat.count (fun k => w k = 1) 2 = 1 := by decide
    rw [hc] at h
    simp [a, h]
  · have h := Nat.nth_count (p := fun k => w k = 1) (n := 5) (by decide)
    have hc : Nat.count (fun k => w k = 1) 5 = 2 := by decide
    rw [hc] at h
    simp [a, h]
  · have h := Nat.nth_count (p := fun k => w k = 1) (n := 7) (by decide)
    have hc : Nat.count (fun k => w k = 1) 7 = 3 := by decide
    rw [hc] at h
    simp [a, h]

end OMA.S_oeis_a286051

theorem OMA.solution : type_of% @OMA.S_oeis_a286051.main :=
  OMA.S_oeis_a286051.conjecture
