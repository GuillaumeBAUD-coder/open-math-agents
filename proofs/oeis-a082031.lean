import OMAStatements.S_oeis_a082031

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: first-order relations for a(n) and auxiliary sums (sum splitting, Pascal rule),
-- combined by linear_combination into the stated recurrence.

open OMA.S_oeis_a082031

namespace P_oeis_a082031

def h (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℤ) * (k.factorial : ℤ) * ((k : ℤ) + 1) * 2 ^ (n - k)

lemma choose2 (k : ℕ) : (((k + 2).choose 2 : ℕ) : ℤ) * 2 = ((k : ℤ) + 2) * ((k : ℤ) + 1) := by
  have := Nat.add_one_mul_choose_eq (k + 1) 1
  rw [Nat.choose_one_right] at this
  have h2 : ((k + 1 + 1) * (k + 1) : ℕ) = (k + 1 + 1).choose (1 + 1) * (1 + 1) := this
  have h3 : (((k + 1 + 1) * (k + 1) : ℕ) : ℤ) = (((k + 1 + 1).choose (1 + 1) * (1 + 1) : ℕ) : ℤ) := by
    rw [h2]
  push_cast at h3
  linarith

lemma choose3 (k : ℕ) : (((k + 3).choose 2 : ℕ) : ℤ) = (((k + 2).choose 2 : ℕ) : ℤ) + (k : ℤ) + 2 := by
  have : (k + 2 + 1).choose (1 + 1) = (k + 2).choose 1 + (k + 2).choose (1 + 1) :=
    Nat.choose_succ_succ (k + 2) 1
  rw [Nat.choose_one_right] at this
  have e : k + 3 = k + 2 + 1 := by ring
  rw [e, this]
  push_cast
  ring

lemma succ_choose (n k : ℕ) :
    ((n + 1 : ℕ) : ℤ) * (n.choose k : ℤ) = ((n + 1).choose (k + 1) : ℤ) * ((k : ℤ) + 1) := by
  have := Nat.add_one_mul_choose_eq n k
  exact_mod_cast this

lemma L1 (n : ℕ) : a (n + 1) = ((n : ℤ) + 1) * a n + h (n + 1) := by
  unfold a h
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
  have key : ∀ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ) * ((k + 1 + 2).choose 2 : ℤ)
        * 2 ^ (n + 1 - (k + 1))
      = ((n : ℤ) + 1) * ((n.choose k : ℤ) * (k.factorial : ℤ) * ((k + 2).choose 2 : ℤ)
          * 2 ^ (n - k))
        + ((n + 1).choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ) * (((k + 1 : ℕ) : ℤ) + 1)
          * 2 ^ (n + 1 - (k + 1)) := by
    intro k _
    have e1 : n + 1 - (k + 1) = n - k := by omega
    have e2 : k + 1 + 2 = k + 3 := by ring
    rw [e1, e2, choose3, Nat.factorial_succ]
    have sc := succ_choose n k
    push_cast at sc ⊢
    linear_combination (-(k.factorial : ℤ) * (((k + 2).choose 2 : ℕ) : ℤ) * 2 ^ (n - k)) * sc
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  simp
  ring

lemma L2 (n : ℕ) : h (n + 1) = 2 * a n + 2 * h n := by
  unfold a h
  rw [Finset.sum_range_succ' _ (n + 1), Finset.mul_sum, Finset.mul_sum]
  have key : ∀ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ) * (((k + 1 : ℕ) : ℤ) + 1)
        * 2 ^ (n + 1 - (k + 1))
      = 2 * ((n.choose k : ℤ) * (k.factorial : ℤ) * ((k + 2).choose 2 : ℤ) * 2 ^ (n - k))
        + (n.choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ) * (((k + 1 : ℕ) : ℤ) + 1)
          * 2 ^ (n - k) := by
    intro k _
    have e1 : n + 1 - (k + 1) = n - k := by omega
    rw [e1, Nat.choose_succ_succ, Nat.factorial_succ]
    have c2 := choose2 k
    push_cast at c2 ⊢
    linear_combination (-(n.choose k : ℤ) * (k.factorial : ℤ) * 2 ^ (n - k)) * c2
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  have key2 : ∀ k ∈ Finset.range n,
      (n.choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ) * (((k + 1 : ℕ) : ℤ) + 1)
          * 2 ^ (n - k)
      = 2 * ((n.choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ) * (((k + 1 : ℕ) : ℤ) + 1)
          * 2 ^ (n - (k + 1))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e : n - k = (n - (k + 1)) + 1 := by omega
    rw [e, pow_succ]
    ring
  have s1 : ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ)
        * (((k + 1 : ℕ) : ℤ) + 1) * 2 ^ (n - k)
      = ∑ k ∈ Finset.range n, 2 * ((n.choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ)
          * (((k + 1 : ℕ) : ℤ) + 1) * 2 ^ (n - (k + 1))) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    exact Finset.sum_congr rfl key2
  have s2 := Finset.sum_range_succ' (fun k => 2 * ((n.choose k : ℤ) * (k.factorial : ℤ)
      * ((k : ℤ) + 1) * 2 ^ (n - k))) n
  rw [s1, s2]
  simp
  ring

theorem main_proved : ∀ n : ℕ, 2 ≤ n →
    a n + (-(n : ℤ) - 4) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  have h1 := L1 (m + 1)
  have h2 := L1 m
  have h3 := L2 (m + 1)
  push_cast at h1 h2 h3 ⊢
  linear_combination h1 + h3 - 2 * h2

end P_oeis_a082031

theorem OMA.solution : type_of% @OMA.S_oeis_a082031.main := P_oeis_a082031.main_proved
