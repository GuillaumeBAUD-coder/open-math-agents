import OMAStatements.S_oeis_a246697

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: row x0 x1 (2j) = x0+2j, row x0 x1 (2j+1) = x1+2j; closed forms for the first two entries
-- of each row by induction on n (by parity), hence the row sum; the recurrence is a linear
-- combination of the closed form at seven consecutive n.

namespace OMA.S_oeis_a246697



lemma row_even (x0 x1 : ℤ) (j : ℕ) : row x0 x1 (2 * j) = x0 + 2 * (j : ℤ) := by
  induction j with
  | zero => simp [row]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, row, ih]; push_cast; ring

lemma row_odd (x0 x1 : ℤ) (j : ℕ) : row x0 x1 (2 * j + 1) = x1 + 2 * (j : ℤ) := by
  induction j with
  | zero => simp [row]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, row, ih]; push_cast; ring

lemma row_sum (x0 x1 : ℤ) (j : ℕ) :
    ∑ k ∈ Finset.range (2 * j), row x0 x1 k = (j : ℤ) * (x0 + x1) + 2 * (j : ℤ) * ((j : ℤ) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, row_even, row_odd]
    push_cast; ring

lemma t_both (m : ℕ) :
    t (2 * m + 2) = row (2 * (m : ℤ) ^ 2 + 6 * m + 5) (2 * (m : ℤ) ^ 2 + 4 * m + 4) ∧
    t (2 * m + 3) = row (2 * (m : ℤ) ^ 2 + 6 * m + 6) (2 * (m : ℤ) ^ 2 + 8 * m + 9) := by
  have hev : ∀ m : ℕ, t (2 * m + 1) (2 * m) = 2 * (m : ℤ) ^ 2 + 4 * m + 2 →
      t (2 * m + 1) (2 * m + 1) = 2 * (m : ℤ) ^ 2 + 6 * m + 3 →
      t (2 * m + 2) = row (2 * (m : ℤ) ^ 2 + 6 * m + 5) (2 * (m : ℤ) ^ 2 + 4 * m + 4) := by
    intro m h1 h2
    show t ((2 * m) + 2) = _
    rw [t.eq_3]
    have hp : (2 * m + 2) % 2 = 0 := by omega
    simp only [hp, show ((0:ℕ) = 1) = False from by simp, if_false]
    rw [h1, h2]; congr 1
  have hod : ∀ m : ℕ,
      t (2 * m + 2) = row (2 * (m : ℤ) ^ 2 + 6 * m + 5) (2 * (m : ℤ) ^ 2 + 4 * m + 4) →
      t (2 * m + 3) = row (2 * (m : ℤ) ^ 2 + 6 * m + 6) (2 * (m : ℤ) ^ 2 + 8 * m + 9) := by
    intro m h
    show t ((2 * m + 1) + 2) = _
    rw [t.eq_3]
    have hp : (2 * m + 1 + 2) % 2 = 1 := by omega
    simp only [hp, if_true]
    rw [h, row_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, row_even]
    push_cast; congr 1 <;> ring
  induction m with
  | zero =>
    have h0 := hev 0 (by simp [t]) (by simp [t])
    norm_num at h0 ⊢
    exact ⟨h0, by simpa using hod 0 (by simpa using h0)⟩
  | succ m ih =>
    have h1 : t (2 * (m + 1) + 1) (2 * (m + 1)) = 2 * ((m + 1 : ℕ) : ℤ) ^ 2 + 4 * ((m + 1 : ℕ) : ℤ) + 2 := by
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, ih.2, row_even]; push_cast; ring
    have h2 : t (2 * (m + 1) + 1) (2 * (m + 1) + 1) = 2 * ((m + 1 : ℕ) : ℤ) ^ 2 + 6 * ((m + 1 : ℕ) : ℤ) + 3 := by
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, ih.2, show 2 * m + 3 = 2 * (m + 1) + 1 by ring, row_odd]; push_cast; ring
    have he := hev (m + 1) h1 h2
    exact ⟨he, hod (m + 1) he⟩

lemma closed (n : ℕ) :
    4 * a n = 2 * (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 9 * (n : ℤ) + 4 + (n : ℤ) * (-1) ^ n := by
  rcases n with _ | _ | n
  · simp [a, t]
  · simp [a, t, Finset.sum_range_succ]
  · rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hs : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
      rw [hs]
      unfold a
      rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, (t_both m).1, Finset.sum_range_succ,
        show 2 * m + 2 = 2 * (m + 1) by ring, row_sum, row_even]
      push_cast; ring
    · have hs : (-1 : ℤ) ^ (2 * m + 1 + 1 + 1) = -1 := Odd.neg_one_pow ⟨m + 1, by ring⟩
      rw [hs]
      unfold a
      rw [show 2 * m + 1 + 1 + 1 = 2 * m + 3 by ring, (t_both m).2,
        show 2 * m + 3 + 1 = 2 * (m + 2) by ring, row_sum]
      push_cast; ring

end OMA.S_oeis_a246697

open OMA.S_oeis_a246697 in
theorem OMA.solution : type_of% @OMA.S_oeis_a246697.main := by
  refine ⟨closed, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  have h0 := closed k
  have h1 := closed (k + 1)
  have h2 := closed (k + 2)
  have h3 := closed (k + 3)
  have h4 := closed (k + 4)
  have h5 := closed (k + 5)
  have h6 := closed (k + 6)
  push_cast at h1 h2 h3 h4 h5 h6
  have : 4 * a (k + 6) = 4 * (2 * a (k + 5) + a (k + 4) - 4 * a (k + 3) + a (k + 2) + 2 * a (k + 1) - a k) := by
    linear_combination h6 - 2 * h5 - h4 + 4 * h3 - h2 - 2 * h1 + h0
  linarith
