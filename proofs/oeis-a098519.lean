import OMAStatements.S_oeis_a098519

-- Problem: A098519: E.g.f. exp(x)*BesselI(1,2*sqrt(3)*x)/sqrt(3).
-- Upstream: statements/oeis-a098519.lean (declaration OMA.S_oeis_a098519.main)
-- Proof: creative telescoping. With T n k the k-th summand of a n and G m k = -4 k (k+1) T (m+2) k,
-- the recurrence operator applied to T telescopes to G m (k+1) - G m k; summing over k gives 0.

namespace OMA.A098519Proof

open OMA.S_oeis_a098519 Finset

/-- The summand of `a n`, with the factor `n!` moved inside. -/
noncomputable def T (n k : ℕ) : ℚ :=
  if 2 * k + 1 ≤ n then
    (n.factorial : ℚ) * ((3 : ℚ) ^ k /
      ((k.factorial : ℚ) * ((k + 1).factorial : ℚ) * ((n - 2 * k - 1).factorial : ℚ)))
  else 0

lemma T_eq_zero {n k : ℕ} (h : n < 2 * k + 1) : T n k = 0 := by
  simp [T, show ¬ (2 * k + 1 ≤ n) by omega]

lemma a_eq (n N : ℕ) (hN : n / 2 + 1 ≤ N) : a n = ∑ k ∈ range N, T n k := by
  have h1 : a n = ∑ k ∈ range (n / 2 + 1), T n k := by
    unfold a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    unfold T
    split_ifs <;> simp
  rw [h1]
  apply Finset.sum_subset (Finset.range_subset_range.2 hN)
  intro k _ hk
  simp only [Finset.mem_range, not_lt] at hk
  exact T_eq_zero (by omega)

/-- The telescoping certificate. -/
noncomputable def G (m k : ℕ) : ℚ := -4 * (k : ℚ) * ((k : ℚ) + 1) * T (m + 2) k

lemma key (m k : ℕ) :
    ((m : ℚ) + 1) * ((m : ℚ) + 3) * T (m + 2) k
      - ((m : ℚ) + 2) * (2 * (m : ℚ) + 3) * T (m + 1) k
      - 11 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * T m k
      = G m (k + 1) - G m k := by
  unfold G
  rcases Nat.lt_or_ge m (2 * k + 1) with h | h
  · -- m ≤ 2k : T m k = 0
    rw [T_eq_zero (n := m) h]
    rcases Nat.lt_or_ge m (2 * k) with h' | h'
    · rw [T_eq_zero (n := m + 1) (by omega), T_eq_zero (n := m + 2) (k := k + 1) (by omega)]
      rcases Nat.lt_or_ge m (2 * k - 1) with h'' | h''
      · rw [T_eq_zero (n := m + 2) (by omega)]; ring
      · -- m = 2k - 1, k ≥ 1
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hm : m = 2 * k' + 1 := by omega
        subst hm
        unfold T
        rw [if_pos (by omega)]
        have e : 2 * k' + 1 + 2 - 2 * (k' + 1) - 1 = 0 := by omega
        rw [e]
        push_cast
        simp only [Nat.factorial_succ, Nat.factorial_zero]
        push_cast
        field_simp
        ring
    · -- m = 2k
      have hm : m = 2 * k := by omega
      subst hm
      rw [T_eq_zero (n := 2 * k + 2) (k := k + 1) (by omega)]
      unfold T
      rw [if_pos (by omega), if_pos (by omega)]
      have e1 : 2 * k + 2 - 2 * k - 1 = 1 := by omega
      have e2 : 2 * k + 1 - 2 * k - 1 = 0 := by omega
      rw [e1, e2]
      push_cast
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      field_simp
      ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = 2 * k + 1 + j := ⟨m - (2 * k + 1), by omega⟩
    unfold T
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have e1 : 2 * k + 1 + j + 2 - 2 * k - 1 = j + 2 := by omega
    have e2 : 2 * k + 1 + j + 1 - 2 * k - 1 = j + 1 := by omega
    have e3 : 2 * k + 1 + j - 2 * k - 1 = j := by omega
    have e4 : 2 * k + 1 + j + 2 - 2 * (k + 1) - 1 = j := by omega
    rw [e1, e2, e3, e4]
    have f1 : (2 * k + 1 + j + 2).factorial
        = (2 * k + j + 3) * ((2 * k + j + 2) * (2 * k + 1 + j).factorial) := by
      rw [show 2 * k + 1 + j + 2 = (2 * k + 1 + j + 1) + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]; ring_nf
    have f2 : (2 * k + 1 + j + 1).factorial = (2 * k + j + 2) * (2 * k + 1 + j).factorial := by
      rw [Nat.factorial_succ]; ring_nf
    rw [f1, f2]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.A098519Proof

open OMA.A098519Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a098519.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  rw [a_eq (m + 2) (m + 2) (by omega), a_eq (m + 1) (m + 2) (by omega),
    a_eq m (m + 2) (by omega)]
  push_cast
  have h3 : (((m : ℚ) + 2 - 1) * ((m : ℚ) + 2 + 1)) = ((m : ℚ) + 1) * ((m : ℚ) + 3) := by ring
  have h4 : ((m : ℚ) + 2) * (2 * ((m : ℚ) + 2) - 1) = ((m : ℚ) + 2) * (2 * (m : ℚ) + 3) := by ring
  have h5 : 11 * ((m : ℚ) + 2) * ((m : ℚ) + 2 - 1) = 11 * ((m : ℚ) + 2) * ((m : ℚ) + 1) := by ring
  rw [h3, h4, h5, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun k _ => key m k), Finset.sum_range_sub (G m)]
  unfold G
  rw [T_eq_zero (n := m + 2) (k := m + 2) (by omega)]
  simp
