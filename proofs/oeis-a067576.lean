import OMAStatements.S_oeis_a067576

/-! OEIS A067576. With P i the numbers having i binary ones, the map x to 2x+1 is an order
preserving bijection from P i onto the odd members of P (i+1), and the first i+1 members of
P (i+1) are all odd (every even member is at least 2^(i+2)-2). So the rank j entries double
(after adding one) from row max 1 j on, while at row j-1 the rank j entry of the next row is even,
which breaks the doubling by parity. -/

namespace OMA.A067576

/-- Numbers with exactly `i` binary ones. -/
abbrev P (i : ℕ) : ℕ → Prop := fun a => a.bitIndices.length = i

lemma pop_odd (n : ℕ) : (2 * n + 1).bitIndices.length = n.bitIndices.length + 1 := by
  simp [Nat.bitIndices_two_mul_add_one]

lemma pop_even (n : ℕ) : (2 * n).bitIndices.length = n.bitIndices.length := by
  simp [Nat.bitIndices_two_mul]

lemma two_pow_pop_le (z : ℕ) : 2 ^ z.bitIndices.length ≤ z + 1 := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · simp
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' z
    · rw [pop_even]
      have := ih m (by omega)
      omega
    · rw [pop_odd, pow_succ]
      have := ih m (by omega)
      omega

lemma pop_pow_sub_one (k : ℕ) : (2 ^ k - 1).bitIndices.length = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := Nat.one_le_two_pow (n := k)
    have : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by rw [pow_succ]; omega
    rw [this, pop_odd, ih]

/-- Counting numbers with `i + 1` ones below `2x+1`: odd ones come from numbers with `i` ones
below `x`, even ones from numbers with `i + 1` ones up to `x`. -/
lemma count_odd (i x : ℕ) :
    Nat.count (P (i + 1)) (2 * x + 1) = Nat.count (P i) x + Nat.count (P (i + 1)) (x + 1) := by
  induction x with
  | zero => simp
  | succ x ih =>
    have e1 : 2 * (x + 1) + 1 = (2 * x + 1) + 1 + 1 := by ring
    have e2 : 2 * x + 1 + 1 = 2 * (x + 1) := by ring
    rw [e1, Nat.count_succ, Nat.count_succ, ih, e2, Nat.count_succ (P i),
      Nat.count_succ (P (i + 1)) (x + 1)]
    simp only [P, pop_odd, pop_even]
    split_ifs <;> omega

lemma count_zero_below (i n : ℕ) (hn : n ≤ 2 ^ (i + 1) - 1) : Nat.count (P (i + 1)) n = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, ih (by omega)]
    have := two_pow_pop_le n
    split_ifs with h
    · simp only [P] at h
      rw [h] at this
      omega
    · rfl

lemma count_full (i : ℕ) : Nat.count (P i) (2 ^ (i + 1) - 1) = i + 1 := by
  induction i with
  | zero => simp [Nat.count_succ]
  | succ i ih =>
    have h1 := Nat.one_le_two_pow (n := i + 1)
    have : 2 ^ (i + 1 + 1) - 1 = 2 * (2 ^ (i + 1) - 1) + 1 := by rw [pow_succ]; omega
    rw [this, count_odd, ih]
    have e : 2 ^ (i + 1) - 1 + 1 = (2 ^ (i + 1) - 1) + 1 := rfl
    rw [Nat.count_succ, count_zero_below i _ le_rfl]
    simp [P, pop_pow_sub_one]

lemma exists_of_lt_count {p : ℕ → Prop} [DecidablePred p] {k n : ℕ} (h : k < Nat.count p n) :
    ∃ m < n, p m ∧ Nat.count p m = k := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [Nat.count_succ] at h
    by_cases hk : k < Nat.count p n
    · obtain ⟨m, hm, hpm, hc⟩ := ih hk
      exact ⟨m, by omega, hpm, hc⟩
    · split_ifs at h with hp
      · exact ⟨n, by omega, hp, by omega⟩
      · omega

lemma doubling (i j : ℕ) (hj : j ≤ i) :
    Nat.nth (P (i + 1)) j + 1 = 2 * (Nat.nth (P i) j + 1) := by
  have hlt : j < Nat.count (P i) (2 ^ (i + 1) - 1) := by rw [count_full]; omega
  obtain ⟨m, hm, hpm, hc⟩ := exists_of_lt_count hlt
  have hnth : Nat.nth (P i) j = m := by rw [← hc]; exact Nat.nth_count hpm
  have hp1 : P (i + 1) (2 * m + 1) := by simp only [P] at hpm ⊢; rw [pop_odd, hpm]
  have hc1 : Nat.count (P (i + 1)) (2 * m + 1) = j := by
    rw [count_odd, hc, count_zero_below i _ (by omega), Nat.add_zero]
  have : Nat.nth (P (i + 1)) j = 2 * m + 1 := by rw [← hc1]; exact Nat.nth_count hp1
  rw [this, hnth]; ring

lemma not_doubling (i : ℕ) :
    Nat.nth (P (i + 1)) (i + 1) + 1 ≠ 2 * (Nat.nth (P i) (i + 1) + 1) := by
  intro hEq
  have hlt : i + 1 < Nat.count (P (i + 1)) (2 ^ (i + 1 + 1) - 1) := by rw [count_full]; omega
  obtain ⟨m, hm, hpm, hc⟩ := exists_of_lt_count hlt
  have hnth : Nat.nth (P (i + 1)) (i + 1) = m := by
    have := Nat.nth_count hpm; rwa [hc] at this
  rw [hnth] at hEq
  obtain ⟨z, rfl⟩ : ∃ z, m = 2 * z + 1 := ⟨m / 2, by omega⟩
  have hpz : P i z := by simp only [P] at hpm ⊢; rw [pop_odd] at hpm; omega
  have h2 : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := pow_succ' 2 (i + 1)
  have hz : z + 1 ≤ 2 ^ (i + 1) - 1 := by omega
  rw [count_odd, count_zero_below i _ hz] at hc
  have hmono := Nat.count_monotone (P i) hz
  rw [Nat.count_succ, if_pos hpz, count_full] at hmono
  omega

end OMA.A067576

open OMA.A067576 in
theorem OMA.solution : type_of% @OMA.S_oeis_a067576.main := by
  intro j
  have key : ∀ i, OMA.S_oeis_a067576.entry i (j + 1) = Nat.nth (P i) j := fun i => by
    simp [OMA.S_oeis_a067576.entry]
  refine ⟨⟨by omega, fun i hi => ?_⟩, fun r ⟨hr0, hr⟩ => ?_⟩
  · rw [key, key]; exact doubling i j (by omega)
  · by_contra hlt
    have h := hr (j - 1) (by omega)
    rw [key, key] at h
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at h
    exact not_doubling (i + 1) h
