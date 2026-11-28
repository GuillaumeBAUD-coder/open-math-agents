import OMAStatements.S_oeis_a158233

open OMA.S_oeis_a158233

lemma sameRow : ∀ x y : ZMod 9,
    ((x ^ 2 - y ^ 2) * (x ^ 2 - (y + 1) ^ 2)).val = 0 ∨
      ((x ^ 2 - y ^ 2) * (x ^ 2 - (y + 1) ^ 2)).val = 3 ∨
        ((x ^ 2 - y ^ 2) * (x ^ 2 - (y + 1) ^ 2)).val = 4 ∨
          ((x ^ 2 - y ^ 2) * (x ^ 2 - (y + 1) ^ 2)).val = 6 := by
  decide

lemma boundary : ∀ x : ZMod 9,
    ((x ^ 2 - (x - 1) ^ 2) * ((x + 1) ^ 2 - 1)).val = 0 ∨
      ((x ^ 2 - (x - 1) ^ 2) * ((x + 1) ^ 2 - 1)).val = 3 ∨
        ((x ^ 2 - (x - 1) ^ 2) * ((x + 1) ^ 2 - 1)).val = 4 ∨
          ((x ^ 2 - (x - 1) ^ 2) * ((x + 1) ^ 2 - 1)).val = 6 := by
  decide

lemma pos_bounds (i : ℕ) : 1 ≤ (pos i).2 ∧ (pos i).2 < (pos i).1 := by
  induction i with
  | zero =>
    rw [pos]
    decide
  | succ i ih =>
    rcases ih with ⟨h1, h2⟩
    simp only [pos, next]
    split_ifs with h
    · constructor <;> omega
    · constructor <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a158233.main := by
  intro n hn
  have hpos : pos n = next (pos (n - 1)) := by
    have hn1 : (n - 1) + 1 = n := by omega
    rw [← hn1]
    rfl
  let m := (pos (n - 1)).1
  let k := (pos (n - 1)).2
  have hbounds := pos_bounds (n - 1)
  have hT1 : T (n + 1) = m ^ 2 - k ^ 2 := by
    have : n + 1 - 2 = n - 1 := by omega
    simp [T, m, k, this]
  have hprod : a n = ((T (n + 1) : ZMod 9) * (T (n + 2) : ZMod 9)).val := by
    simp only [a]
    rw [← ZMod.val_natCast, Nat.cast_mul]
  by_cases hlt : k + 1 < m
  · have hnext : pos n = (m, k + 1) := by
      simp [hpos, next, m, k, hlt]
    have hT2 : T (n + 2) = m ^ 2 - (k + 1) ^ 2 := by
      have : n + 2 - 2 = n := by omega
      simp [T, this, hnext]
    have hsq1 : k ^ 2 ≤ m ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hbounds.2) 2
    have hsq2 : (k + 1) ^ 2 ≤ m ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hlt) 2
    rw [hprod, hT1, hT2, Nat.cast_sub hsq1, Nat.cast_sub hsq2]
    simpa [m, k] using sameRow (m : ZMod 9) (k : ZMod 9)
  · have hk : k = m - 1 := by
      have hklt : k < m := hbounds.2
      omega
    have hnext : pos n = (m + 1, 1) := by
      simp [hpos, next, m, k, hlt]
    have hT2 : T (n + 2) = (m + 1) ^ 2 - 1 := by
      have : n + 2 - 2 = n := by omega
      simp [T, this, hnext]
    have hsq1 : (m - 1) ^ 2 ≤ m ^ 2 :=
      Nat.pow_le_pow_left (show m - 1 ≤ m by omega) 2
    have hsq2 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow 2 (m + 1) (by omega)
    have hm1 : 1 ≤ m := by omega
    rw [hprod, hT1, hT2, hk, Nat.cast_sub hsq1, Nat.cast_sub hsq2, Nat.cast_pow,
      Nat.cast_pow]
    have hcast : ((m - 1 : ℕ) : ZMod 9) = (m : ZMod 9) - 1 := Nat.cast_sub hm1
    rw [hcast]
    simpa [m] using boundary (m : ZMod 9)
