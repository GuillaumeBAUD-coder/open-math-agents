import OMAStatements.S_oeis_a182025

-- Problem: A182025: a(n) = 31*binomial(2*n,n-4) + Sum_{i=1..n-4} binomial(2*n,n-4-i)*(4+i).
-- Upstream: formal-conjectures statements/oeis-a182025.lean:0 (declaration OMA.S_oeis_a182025.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: Sum_{j<=k} (m+4-j) C(2m+8,j) = (m+4) C(2m+7,k) telescopes the sum, so 2a(n) = (n+58) C(2n,n+4) for all n; with (j+8) j C(2j+8,j+8) = 2(j+4)(2j+7) C(2j+6,j+7) the recurrence is a linear combination.

open OMA.S_oeis_a182025 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182025.main := by
  have hpart : ∀ m k : ℕ, k ≤ 2 * m + 7 →
      ∑ j ∈ Finset.range (k + 1), ((m : ℤ) + 4 - (j : ℤ)) * ((2 * m + 8).choose j : ℤ)
        = ((m : ℤ) + 4) * ((2 * m + 7).choose k : ℤ) := by
    intro m k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, ih (by omega)]
      have p1 := Nat.choose_succ_succ' (2 * m + 7) k
      rw [show 2 * m + 7 + 1 = 2 * m + 8 by omega] at p1
      have p2 := Nat.choose_succ_right_eq (2 * m + 7) k
      have p1' : ((2 * m + 8).choose (k + 1) : ℤ)
          = ((2 * m + 7).choose k : ℤ) + ((2 * m + 7).choose (k + 1) : ℤ) := by
        exact_mod_cast p1
      have p2' : ((2 * m + 7).choose (k + 1) : ℤ) * ((k : ℤ) + 1)
          = ((2 * m + 7).choose k : ℤ) * (2 * (m : ℤ) + 7 - (k : ℤ)) := by
        have h := congrArg (Nat.cast : ℕ → ℤ) p2
        push_cast [Nat.cast_sub (show k ≤ 2 * m + 7 by omega)] at h
        linear_combination h
      push_cast
      linear_combination ((m : ℤ) + 3 - (k : ℤ)) * p1' - p2'
  have hclosed : ∀ n : ℕ, 2 * a n = ((n : ℤ) + 58) * ((2 * n).choose (n + 4) : ℤ) := by
    intro n
    rcases Nat.lt_or_ge n 4 with h | h
    · unfold a
      rw [if_pos h, Nat.choose_eq_zero_of_lt (by omega : 2 * n < n + 4)]
      simp
    rcases Nat.eq_or_lt_of_le h with h4 | h5
    · subst h4
      norm_num [a]
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 5 := ⟨n - 5, by omega⟩
    unfold a
    rw [if_neg (by omega), show p + 5 - 4 = p + 1 by omega]
    have hre : ∑ i ∈ Finset.Icc 1 (p + 1), ((2 * (p + 5)).choose (p + 1 - i) : ℤ) * (4 + (i : ℤ))
        = ∑ j ∈ Finset.range (p + 1),
            (((p + 1 : ℕ) : ℤ) + 4 - (j : ℤ)) * ((2 * (p + 1) + 8).choose j : ℤ) := by
      refine Finset.sum_nbij' (fun i => p + 1 - i) (fun j => p + 1 - j) ?_ ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        simp only [Finset.mem_range]
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        simp only [Finset.mem_Icc]
        omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        show p + 1 - (p + 1 - i) = i
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        show p + 1 - (p + 1 - j) = j
        omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        show ((2 * (p + 5)).choose (p + 1 - i) : ℤ) * (4 + (i : ℤ))
          = (((p + 1 : ℕ) : ℤ) + 4 - ((p + 1 - i : ℕ) : ℤ)) * ((2 * (p + 1) + 8).choose (p + 1 - i) : ℤ)
        rw [show 2 * (p + 1) + 8 = 2 * (p + 5) by ring, Nat.cast_sub hi.2]
        push_cast
        ring
    rw [hre, hpart (p + 1) p (by omega)]
    have hsym : (2 * (p + 5)).choose (p + 5 + 4) = (2 * (p + 5)).choose (p + 1) :=
      Nat.choose_symm_of_eq_add (by ring)
    have habs := Nat.add_one_mul_choose_eq (2 * (p + 1) + 7) p
    rw [show 2 * (p + 1) + 7 + 1 = 2 * (p + 5) by ring] at habs
    have hz : 2 * ((p : ℤ) + 5) * ((2 * (p + 1) + 7).choose p : ℤ)
        = ((2 * (p + 5)).choose (p + 1) : ℤ) * ((p : ℤ) + 1) := by
      exact_mod_cast habs
    rw [hsym]
    push_cast
    linear_combination hz
  have hR : ∀ j : ℕ, ((j : ℤ) + 8) * (j : ℤ) * ((2 * j + 8).choose (j + 8) : ℤ)
      = 2 * ((j : ℤ) + 4) * (2 * (j : ℤ) + 7) * ((2 * j + 6).choose (j + 7) : ℤ) := by
    intro j
    have s1 := Nat.add_one_mul_choose_eq (2 * j + 6) (j + 7)
    have s2 := Nat.choose_mul_succ_eq (2 * j + 7) (j + 8)
    rw [show 2 * j + 6 + 1 = 2 * j + 7 by omega, show j + 7 + 1 = j + 8 by omega] at s1
    rw [show 2 * j + 7 + 1 - (j + 8) = j by omega, show 2 * j + 7 + 1 = 2 * j + 8 by omega] at s2
    have t1 : (2 * (j : ℤ) + 7) * ((2 * j + 6).choose (j + 7) : ℤ)
        = ((2 * j + 7).choose (j + 8) : ℤ) * ((j : ℤ) + 8) := by
      exact_mod_cast s1
    have t2 : ((2 * j + 7).choose (j + 8) : ℤ) * (2 * (j : ℤ) + 8)
        = ((2 * j + 8).choose (j + 8) : ℤ) * (j : ℤ) := by
      exact_mod_cast s2
    linear_combination -((j : ℤ) + 8) * t2 - (2 * (j : ℤ) + 8) * t1
  intro n hn
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> norm_num [a]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
  have h2 := hclosed (m + 5)
  have h1 := hclosed (m + 4)
  have h0 := hclosed (m + 3)
  have R1 := hR (m + 1)
  have R0 := hR m
  rw [show 2 * (m + 5) = 2 * m + 10 by ring, show m + 5 + 4 = m + 9 by ring] at h2
  rw [show 2 * (m + 4) = 2 * m + 8 by ring, show m + 4 + 4 = m + 8 by ring] at h1
  rw [show 2 * (m + 3) = 2 * m + 6 by ring, show m + 3 + 4 = m + 7 by ring] at h0
  rw [show 2 * (m + 1) + 8 = 2 * m + 10 by ring, show m + 1 + 8 = m + 9 by ring,
    show 2 * (m + 1) + 6 = 2 * m + 8 by ring, show m + 1 + 7 = m + 8 by ring] at R1
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  push_cast at h2 h1 h0 R1 ⊢
  linear_combination 558 * ((m : ℤ) + 1) * ((m : ℤ) + 9) * h2
    + 7 * (-631 * ((m : ℤ) + 5) ^ 2 + 777 * ((m : ℤ) + 5) + 4600) * h1
    + 4370 * ((m : ℤ) + 4) * (2 * (m : ℤ) + 7) * h0
    + 558 * ((m : ℤ) + 63) * R1 - 2185 * ((m : ℤ) + 61) * R0
