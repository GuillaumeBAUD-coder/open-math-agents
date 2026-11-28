import OMAStatements.S_oeis_a024719

theorem OMA.solution : type_of% @OMA.S_oeis_a024719.main := by
  -- ratio of consecutive terms C(3j,j): 2(j+1)(2j+1) C(3j+3,j+1) = 3(3j+2)(3j+1) C(3j,j)
  have key : ∀ j : ℕ, (2 * ((j : ℚ) + 1) * (2 * j + 1)) * ((3 * (j + 1)).choose (j + 1) : ℚ)
      = 3 * (3 * j + 2) * (3 * j + 1) * ((3 * j).choose j : ℚ) := by
    intro j
    have h1 : (3 * j + 3) * (3 * j + 2).choose j = (3 * j + 3).choose (j + 1) * (j + 1) := by
      first
        | exact Nat.add_one_mul_choose_eq (3 * j + 2) j
        | (have a := Nat.choose_succ_right_eq (3 * j + 3) j
           have b := Nat.choose_mul_succ_eq (3 * j + 2) j
           have ea : 3 * j + 3 - j = 2 * j + 3 := by omega
           have eb : 3 * j + 2 + 1 - j = 2 * j + 3 := by omega
           rw [ea] at a
           rw [eb] at b
           have b' : (3 * j + 3) * (3 * j + 2).choose j = (3 * j + 3).choose j * (2 * j + 3) := by
             rw [mul_comm]
             exact b
           exact b'.trans a.symm)
    have e2 : 3 * j + 1 + 1 - j = 2 * j + 2 := by omega
    have e3 : 3 * j + 1 - j = 2 * j + 1 := by omega
    have h2 : (3 * j + 1).choose j * (3 * j + 2) = (3 * j + 2).choose j * (2 * j + 2) :=
      (Nat.choose_mul_succ_eq (3 * j + 1) j).trans (congrArg (fun x => (3 * j + 2).choose j * x) e2)
    have h3 : (3 * j).choose j * (3 * j + 1) = (3 * j + 1).choose j * (2 * j + 1) :=
      (Nat.choose_mul_succ_eq (3 * j) j).trans (congrArg (fun x => (3 * j + 1).choose j * x) e3)
    have h1q : ((3 : ℚ) * j + 3) * ((3 * j + 2).choose j : ℚ)
        = ((3 * j + 3).choose (j + 1) : ℚ) * (j + 1) := by exact_mod_cast h1
    have h2q : ((3 * j + 1).choose j : ℚ) * ((3 : ℚ) * j + 2)
        = ((3 * j + 2).choose j : ℚ) * (2 * j + 2) := by exact_mod_cast h2
    have h3q : ((3 * j).choose j : ℚ) * ((3 : ℚ) * j + 1)
        = ((3 * j + 1).choose j : ℚ) * (2 * j + 1) := by exact_mod_cast h3
    have e : 3 * (j + 1) = 3 * j + 3 := by ring
    rw [e]
    linear_combination (-2 * (2 * (j : ℚ) + 1)) * h1q - 3 * (2 * (j : ℚ) + 1) * h2q
      - 3 * (3 * (j : ℚ) + 2) * h3q
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  have hk := key (m + 1)
  have hS1 : ∑ k ∈ Finset.range (m + 1 + 1), ((3 * k).choose k : ℚ)
      = ∑ k ∈ Finset.range (m + 1), ((3 * k).choose k : ℚ)
        + ((3 * (m + 1)).choose (m + 1) : ℚ) := Finset.sum_range_succ _ _
  have hS2 : ∑ k ∈ Finset.range (m + 2 + 1), ((3 * k).choose k : ℚ)
      = ∑ k ∈ Finset.range (m + 1), ((3 * k).choose k : ℚ)
        + ((3 * (m + 1)).choose (m + 1) : ℚ)
        + ((3 * (m + 1 + 1)).choose (m + 1 + 1) : ℚ) := by
    calc ∑ k ∈ Finset.range (m + 2 + 1), ((3 * k).choose k : ℚ)
        = ∑ k ∈ Finset.range (m + 1 + 1), ((3 * k).choose k : ℚ)
          + ((3 * (m + 1 + 1)).choose (m + 1 + 1) : ℚ) := Finset.sum_range_succ _ (m + 2)
      _ = _ := by rw [hS1]
  have c1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by norm_num
  have c2 : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by norm_num
  unfold OMA.S_oeis_a024719.a
  rw [hS2, hS1, c2]
  rw [c1] at hk
  linear_combination (1 / 3 : ℚ) * hk
