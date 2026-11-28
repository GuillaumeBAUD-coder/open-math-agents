import OMAStatements.S_oeis_a295687

open OMA.S_oeis_a295687 in
theorem OMA.solution : type_of% @OMA.S_oeis_a295687.main := by
  have key : ∀ m, a (m + 4) = a (m + 3) + a (m + 1) + a m := fun m => rfl
  -- e(m) = a(m+4) - 3 a(m+2) + a(m) obeys the same recurrence as a
  have hrec : ∀ m, a (m + 8) - 3 * a (m + 6) + a (m + 4) =
      (a (m + 7) - 3 * a (m + 5) + a (m + 3)) + (a (m + 5) - 3 * a (m + 3) + a (m + 1)) +
        (a (m + 4) - 3 * a (m + 2) + a m) := by
    intro m
    have h1 : a (m + 8) = a (m + 7) + a (m + 5) + a (m + 4) := key (m + 4)
    have h2 : a (m + 6) = a (m + 5) + a (m + 3) + a (m + 2) := key (m + 2)
    have h3 : a (m + 4) = a (m + 3) + a (m + 1) + a m := key m
    rw [h1, h2, h3]
    ring
  -- e is periodic with values -1, 7, 1, -7
  have per : ∀ k : ℕ,
      a (4 * k + 4) - 3 * a (4 * k + 2) + a (4 * k) = -1 ∧
      a (4 * k + 5) - 3 * a (4 * k + 3) + a (4 * k + 1) = 7 ∧
      a (4 * k + 6) - 3 * a (4 * k + 4) + a (4 * k + 2) = 1 ∧
      a (4 * k + 7) - 3 * a (4 * k + 5) + a (4 * k + 3) = -7 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      obtain ⟨e0, e1, e2, e3⟩ := ih
      have r0 := hrec (4 * k)
      have r1 := hrec (4 * k + 1)
      have r2 := hrec (4 * k + 2)
      have r3 := hrec (4 * k + 3)
      have q : 4 * (k + 1) = 4 * k + 4 := by ring
      rw [q]
      simp only [add_assoc, Nat.reduceAdd] at r0 r1 r2 r3 e0 e1 e2 e3 ⊢
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  intro n hn
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
    · exact ⟨j - 1, Or.inl (by omega)⟩
    · exact ⟨j - 1, Or.inr (by omega)⟩
  · obtain ⟨e0, e1, -, -⟩ := per k
    have i1 : 2 * (2 * k + 2) = 4 * k + 4 := by ring
    have i2 : 2 * (2 * k + 2) - 2 = 4 * k + 2 := by omega
    have i3 : 2 * (2 * k + 2) - 4 = 4 * k := by omega
    have i4 : 2 * (2 * k + 2) + 1 = 4 * k + 5 := by ring
    have i5 : 2 * (2 * k + 2) - 1 = 4 * k + 3 := by omega
    have i6 : 2 * (2 * k + 2) - 3 = 4 * k + 1 := by omega
    have s : ((-1 : ℤ)) ^ (2 * k + 2) = 1 := by
      rw [pow_add, pow_mul]; norm_num
    rw [i2, i3, i4, i5, i6, i1, s]
    constructor <;> linarith
  · obtain ⟨-, -, e2, e3⟩ := per k
    have i1 : 2 * (2 * k + 3) = 4 * k + 6 := by ring
    have i2 : 2 * (2 * k + 3) - 2 = 4 * k + 4 := by omega
    have i3 : 2 * (2 * k + 3) - 4 = 4 * k + 2 := by omega
    have i4 : 2 * (2 * k + 3) + 1 = 4 * k + 7 := by ring
    have i5 : 2 * (2 * k + 3) - 1 = 4 * k + 5 := by omega
    have i6 : 2 * (2 * k + 3) - 3 = 4 * k + 3 := by omega
    have s : ((-1 : ℤ)) ^ (2 * k + 3) = -1 := by
      rw [pow_add, pow_mul]; norm_num
    rw [i2, i3, i4, i5, i6, i1, s]
    constructor <;> linarith
