import OMAStatements.S_oeis_a099576

namespace OMA.P_oeis_a099576

open Finset OMA.S_oeis_a099576

private lemma sum_choose_add (n m : ℕ) :
    ∑ j ∈ range (m + 1), (n + j).choose j = (n + m + 1).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    have h1 : n + (m + 1) = n + m + 1 := by omega
    rw [h1]
    exact (Nat.choose_succ_succ (n + m + 1) m).symm

private lemma mul_choose_succ_succ (k r : ℕ) :
    (r + 1) * (k + 1).choose (r + 1) = (k + 1) * k.choose r := by
  induction k generalizing r with
  | zero =>
    cases r with
    | zero => simp
    | succ r => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < r + 1 + 1)]
  | succ k ih =>
    cases r with
    | zero => simp
    | succ r =>
      have h1 := ih r
      have h2 := ih (r + 1)
      have h3 : (k + 1).choose (r + 1) = k.choose r + k.choose (r + 1) :=
        Nat.choose_succ_succ k r
      have h4 : (k + 1 + 1).choose (r + 1 + 1) =
          (k + 1).choose (r + 1) + (k + 1).choose (r + 1 + 1) :=
        Nat.choose_succ_succ (k + 1) (r + 1)
      calc (r + 1 + 1) * (k + 1 + 1).choose (r + 1 + 1)
          = (r + 1 + 1) * ((k + 1).choose (r + 1) + (k + 1).choose (r + 1 + 1)) := by rw [h4]
        _ = (r + 1) * (k + 1).choose (r + 1) + (k + 1).choose (r + 1) +
              (r + 1 + 1) * (k + 1).choose (r + 1 + 1) := by ring
        _ = (k + 1) * k.choose r + (k.choose r + k.choose (r + 1)) +
              (k + 1) * k.choose (r + 1) := by rw [h1, h2, h3]
        _ = (k + 1 + 1) * (k.choose r + k.choose (r + 1)) := by ring
        _ = (k + 1 + 1) * (k + 1).choose (r + 1) := by rw [← h3]

private lemma sum_mul_choose_add (n m : ℕ) :
    ∑ j ∈ range (m + 1), j * (n + j).choose j =
      if m = 0 then 0 else (n + 1) * (n + m + 1).choose (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    cases m with
    | zero =>
      simp [Nat.choose_one_right]
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hterm : (m + 2) * (n + (m + 2)).choose (m + 2) =
          (n + 1) * (n + (m + 2)).choose (m + 1) := by
        have h4 : (n + (m + 2) - (m + 1)) * (n + (m + 2)).choose (m + 1) =
            (n + (m + 2)).choose (m + 2) * (m + 2) := by
          have := Nat.choose_succ_right_eq (n + (m + 2)) (m + 1)
          linarith
        have h5 : n + (m + 2) - (m + 1) = n + 1 := by omega
        rw [h5] at h4
        linarith
      rw [hterm, ← mul_add]
      congr 1

private lemma a_eq_single_sum (n : ℕ) :
    a n = ∑ j ∈ range (n / 2 + 1), (n + 1 - 2 * j) * (n + j).choose j := by
  unfold a
  have h1 : ∑ k ∈ range (n + 1), ∑ j ∈ range (k / 2 + 1), (n + j).choose j =
      ∑ k ∈ range (n + 1), ∑ j ∈ range (n / 2 + 1),
        if 2 * j ≤ k then (n + j).choose j else 0 := by
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [mem_range, mem_filter]
    omega
  rw [h1, sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [← sum_filter, sum_const, smul_eq_mul]
  congr 1
  have hcard : (filter (fun k => 2 * j ≤ k) (range (n + 1))) = Ico (2 * j) (n + 1) := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hcard, Nat.card_Ico]

private lemma a_closed_even (m : ℕ) :
    ((m + 1 : ℤ)) * (a (2 * m) : ℤ) = (2 * (m : ℤ) + 1) * ((3 * m + 1).choose m : ℤ) := by
  rw [a_eq_single_sum (2 * m)]
  have hdiv : 2 * m / 2 = m := by omega
  rw [hdiv]
  have hcast :
      ((∑ j ∈ range (m + 1), (2 * m + 1 - 2 * j) * (2 * m + j).choose j : ℕ) : ℤ) =
        (2 * (m : ℤ) + 1) * ((∑ j ∈ range (m + 1), (2 * m + j).choose j : ℕ) : ℤ) -
          2 * ((∑ j ∈ range (m + 1), j * (2 * m + j).choose j : ℕ) : ℤ) := by
    push_cast
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    have hle : 2 * j ≤ 2 * m + 1 := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hcast, sum_choose_add, sum_mul_choose_add]
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hrel : (2 * (m + 1) + 2) * (3 * (m + 1) + 1).choose m =
        (m + 1) * (3 * (m + 1) + 1).choose (m + 1) := by
      have h := Nat.choose_succ_right_eq (3 * (m + 1) + 1) m
      have hsub : 3 * (m + 1) + 1 - m = 2 * (m + 1) + 2 := by omega
      rw [hsub] at h
      linarith
    have hrelZ : (2 * ((m + 1 : ℕ) : ℤ) + 2) * ((3 * (m + 1) + 1).choose m : ℤ) =
        ((m + 1 : ℕ) : ℤ) * ((3 * (m + 1) + 1).choose (m + 1) : ℤ) := by
      exact_mod_cast hrel
    have h3 : 2 * (m + 1) + (m + 1) + 1 = 3 * (m + 1) + 1 := by omega
    rw [h3]
    push_cast at hrelZ ⊢
    nlinarith

private lemma a_closed_odd (m : ℕ) :
    (2 * (m : ℤ) + 3) * (a (2 * m + 1) : ℤ) =
      3 * (2 * (m : ℤ) + 2) * ((3 * m + 2).choose m : ℤ) := by
  rw [a_eq_single_sum (2 * m + 1)]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hdiv]
  have hcast :
      ((∑ j ∈ range (m + 1), (2 * m + 1 + 1 - 2 * j) * (2 * m + 1 + j).choose j : ℕ) : ℤ) =
        (2 * (m : ℤ) + 2) * ((∑ j ∈ range (m + 1), (2 * m + 1 + j).choose j : ℕ) : ℤ) -
          2 * ((∑ j ∈ range (m + 1), j * (2 * m + 1 + j).choose j : ℕ) : ℤ) := by
    push_cast
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    have hle : 2 * j ≤ 2 * m + 1 + 1 := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hcast, sum_choose_add, sum_mul_choose_add]
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hrel : (2 * (m + 1) + 3) * (3 * (m + 1) + 2).choose m =
        (m + 1) * (3 * (m + 1) + 2).choose (m + 1) := by
      have h := Nat.choose_succ_right_eq (3 * (m + 1) + 2) m
      have hsub : 3 * (m + 1) + 2 - m = 2 * (m + 1) + 3 := by omega
      rw [hsub] at h
      linarith
    have hrelZ : (2 * ((m + 1 : ℕ) : ℤ) + 3) * ((3 * (m + 1) + 2).choose m : ℤ) =
        ((m + 1 : ℕ) : ℤ) * ((3 * (m + 1) + 2).choose (m + 1) : ℤ) := by
      exact_mod_cast hrel
    have h3 : 2 * (m + 1) + 1 + (m + 1) + 1 = 3 * (m + 1) + 2 := by omega
    rw [h3]
    push_cast at hrelZ ⊢
    nlinarith

private lemma choose_step1 (k r : ℕ) (h : r ≤ k) :
    ((k + 1 - r : ℕ) : ℤ) * ((k + 1).choose r : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.choose r : ℤ) := by
  have hnat : (k + 1 - r) * (k + 1).choose r = (k + 1) * k.choose r := by
    have hsym : (k + 1).choose (k + 1 - r) = (k + 1).choose r :=
      Nat.choose_symm (by omega)
    have hsym2 : k.choose (k - r) = k.choose r := Nat.choose_symm h
    rw [← hsym, ← hsym2]
    have h3 := mul_choose_succ_succ k (k - r)
    have h4 : k - r + 1 = k + 1 - r := by omega
    rw [h4] at h3
    exact h3
  exact_mod_cast hnat

private lemma choose_step2 (k r : ℕ) :
    ((r + 1 : ℕ) : ℤ) * ((k + 1).choose (r + 1) : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.choose r : ℤ) := by
  exact_mod_cast mul_choose_succ_succ k r

private lemma recurrence_even (m : ℕ) (hm : 1 ≤ m) :
    4 * (2 * (m : ℤ)) * (2 * (m : ℤ) - 1) * (3 * (2 * (m : ℤ)) + 2) * (2 * (m : ℤ) + 2) *
        (a (2 * m) : ℤ) -
      36 * (2 * (m : ℤ) - 1) * (2 * (m : ℤ) + 1) * (a (2 * m - 1) : ℤ) -
      3 * (2 * (m : ℤ)) * (3 * (2 * (m : ℤ)) + 5) * (3 * (2 * (m : ℤ)) - 1) *
        (3 * (2 * (m : ℤ)) - 2) * (a (2 * m - 2) : ℤ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have he1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have he2 : 2 * (k + 1) - 2 = 2 * k := by omega
  rw [he1, he2]
  have hA := a_closed_even (k + 1)
  have hB := a_closed_odd k
  have hC := a_closed_even k
  set C0 : ℤ := ((3 * k + 1).choose k : ℤ)
  set C1 : ℤ := ((3 * k + 2).choose k : ℤ)
  set C2 : ℤ := ((3 * k + 3).choose k : ℤ)
  set C3 : ℤ := ((3 * k + 4).choose (k + 1) : ℤ)
  have r1 : (2 * (k : ℤ) + 2) * C1 = (3 * (k : ℤ) + 2) * C0 := by
    have h := choose_step1 (3 * k + 1) k (by omega)
    have hs : 3 * k + 1 + 1 - k = 2 * k + 2 := by omega
    rw [hs] at h
    push_cast at h
    exact h
  have r2 : (2 * (k : ℤ) + 3) * C2 = (3 * (k : ℤ) + 3) * C1 := by
    have h := choose_step1 (3 * k + 2) k (by omega)
    have hs : 3 * k + 2 + 1 - k = 2 * k + 3 := by omega
    rw [hs] at h
    push_cast at h
    exact h
  have r3 : ((k : ℤ) + 1) * C3 = (3 * (k : ℤ) + 4) * C2 := by
    have h := choose_step2 (3 * k + 3) k
    have hs : 3 * k + 3 + 1 = 3 * k + 4 := by omega
    rw [hs] at h
    push_cast at h
    exact h
  have h34 : 3 * (k + 1) + 1 = 3 * k + 4 := by omega
  rw [h34] at hA
  change ((k + 1 : ℕ) + 1 : ℤ) * (a (2 * (k + 1)) : ℤ) =
    (2 * ((k + 1 : ℕ) : ℤ) + 1) * C3 at hA
  change (2 * (k : ℤ) + 3) * (a (2 * k + 1) : ℤ) = 3 * (2 * (k : ℤ) + 2) * C1 at hB
  change ((k : ℤ) + 1) * (a (2 * k) : ℤ) = (2 * (k : ℤ) + 1) * C0 at hC
  push_cast at hA ⊢
  have hnz : ((k : ℤ) + 1) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) ≠ 0 := by positivity
  apply mul_left_cancel₀ hnz
  rw [mul_zero]
  have hA' : ((k : ℤ) + 2) * (a (2 * (k + 1)) : ℤ) = (2 * (k : ℤ) + 3) * C3 := by linarith
  have hcomb :
      ((k : ℤ) + 1) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) *
        (4 * (2 * ((k : ℤ) + 1)) * (2 * ((k : ℤ) + 1) - 1) *
            (3 * (2 * ((k : ℤ) + 1)) + 2) * (2 * ((k : ℤ) + 1) + 2) * (a (2 * (k + 1)) : ℤ) -
          36 * (2 * ((k : ℤ) + 1) - 1) * (2 * ((k : ℤ) + 1) + 1) * (a (2 * k + 1) : ℤ) -
          3 * (2 * ((k : ℤ) + 1)) * (3 * (2 * ((k : ℤ) + 1)) + 5) *
            (3 * (2 * ((k : ℤ) + 1)) - 1) * (3 * (2 * ((k : ℤ) + 1)) - 2) * (a (2 * k) : ℤ)) =
      (8 * (k : ℤ) + 8) * (2 * (k : ℤ) + 1) * (6 * (k : ℤ) + 8) * (2 * (k : ℤ) + 4) *
          ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * (((k : ℤ) + 2) * (a (2 * (k + 1)) : ℤ)) -
        36 * (2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 3) * ((k : ℤ) + 1) * ((k : ℤ) + 2) *
          ((2 * (k : ℤ) + 3) * (a (2 * k + 1) : ℤ)) -
        6 * ((k : ℤ) + 1) * (6 * (k : ℤ) + 11) * (6 * (k : ℤ) + 5) * (6 * (k : ℤ) + 4) *
          ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * (((k : ℤ) + 1) * (a (2 * k) : ℤ)) := by ring
  rw [hcomb, hA', hB, hC]
  -- Eliminate C3, C2, C1 in favor of C0
  have hC3 : ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * C3 =
      (3 * (k : ℤ) + 4) * (3 * (k : ℤ) + 3) * (3 * (k : ℤ) + 2) * C0 := by
    calc ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * C3
        = (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * (((k : ℤ) + 1) * C3) := by ring
      _ = (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * ((3 * (k : ℤ) + 4) * C2) := by rw [r3]
      _ = (3 * (k : ℤ) + 4) * (2 * (k : ℤ) + 2) * ((2 * (k : ℤ) + 3) * C2) := by ring
      _ = (3 * (k : ℤ) + 4) * (2 * (k : ℤ) + 2) * ((3 * (k : ℤ) + 3) * C1) := by rw [r2]
      _ = (3 * (k : ℤ) + 4) * (3 * (k : ℤ) + 3) * ((2 * (k : ℤ) + 2) * C1) := by ring
      _ = (3 * (k : ℤ) + 4) * (3 * (k : ℤ) + 3) * ((3 * (k : ℤ) + 2) * C0) := by rw [r1]
      _ = (3 * (k : ℤ) + 4) * (3 * (k : ℤ) + 3) * (3 * (k : ℤ) + 2) * C0 := by ring
  have hnz2 : 2 * (k : ℤ) + 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hnz2
  rw [mul_zero]
  have hfinal :
      (2 * (k : ℤ) + 2) *
        ((8 * (k : ℤ) + 8) * (2 * (k : ℤ) + 1) * (6 * (k : ℤ) + 8) * (2 * (k : ℤ) + 4) *
            ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * ((2 * (k : ℤ) + 3) * C3) -
          36 * (2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 3) * ((k : ℤ) + 1) * ((k : ℤ) + 2) *
            (3 * (2 * (k : ℤ) + 2) * C1) -
          6 * ((k : ℤ) + 1) * (6 * (k : ℤ) + 11) * (6 * (k : ℤ) + 5) * (6 * (k : ℤ) + 4) *
            ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * ((2 * (k : ℤ) + 1) * C0)) =
      (8 * (k : ℤ) + 8) * (2 * (k : ℤ) + 1) * (6 * (k : ℤ) + 8) * (2 * (k : ℤ) + 4) *
          (2 * (k : ℤ) + 3) * (((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * C3) -
        108 * (2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 3) * ((k : ℤ) + 1) * ((k : ℤ) + 2) *
          (2 * (k : ℤ) + 2) * ((2 * (k : ℤ) + 2) * C1) -
        6 * (2 * (k : ℤ) + 2) * ((k : ℤ) + 1) * (6 * (k : ℤ) + 11) * (6 * (k : ℤ) + 5) *
          (6 * (k : ℤ) + 4) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 1) * C0 := by
    ring
  rw [hfinal, hC3, r1]
  ring

private lemma recurrence_odd (m : ℕ) (hm : 1 ≤ m) :
    4 * (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1 - 1) * (3 * (2 * (m : ℤ) + 1) + 2) *
        (2 * (m : ℤ) + 1 + 2) * (a (2 * m + 1) : ℤ) -
      36 * (2 * (m : ℤ) + 1 - 1) * (2 * (m : ℤ) + 1 + 1) * (a (2 * m) : ℤ) -
      3 * (2 * (m : ℤ) + 1) * (3 * (2 * (m : ℤ) + 1) + 5) * (3 * (2 * (m : ℤ) + 1) - 1) *
        (3 * (2 * (m : ℤ) + 1) - 2) * (a (2 * m - 1) : ℤ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have he1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [he1]
  have hA := a_closed_odd (k + 1)
  have hB := a_closed_even (k + 1)
  have hC := a_closed_odd k
  set C0 : ℤ := ((3 * k + 2).choose k : ℤ)
  set C1 : ℤ := ((3 * k + 3).choose k : ℤ)
  set C2 : ℤ := ((3 * k + 4).choose (k + 1) : ℤ)
  set C3 : ℤ := ((3 * k + 5).choose (k + 1) : ℤ)
  have r1 : (2 * (k : ℤ) + 3) * C1 = (3 * (k : ℤ) + 3) * C0 := by
    have h := choose_step1 (3 * k + 2) k (by omega)
    have hs : 3 * k + 2 + 1 - k = 2 * k + 3 := by omega
    rw [hs] at h
    push_cast at h
    exact h
  have r2 : ((k : ℤ) + 1) * C2 = (3 * (k : ℤ) + 4) * C1 := by
    have h := choose_step2 (3 * k + 3) k
    have hs : 3 * k + 3 + 1 = 3 * k + 4 := by omega
    rw [hs] at h
    push_cast at h
    exact h
  have r3 : (2 * (k : ℤ) + 4) * C3 = (3 * (k : ℤ) + 5) * C2 := by
    have h := choose_step1 (3 * k + 4) (k + 1) (by omega)
    have hs : 3 * k + 4 + 1 - (k + 1) = 2 * k + 4 := by omega
    rw [hs] at h
    push_cast at h
    exact h
  have h35 : 3 * (k + 1) + 2 = 3 * k + 5 := by omega
  have h34 : 3 * (k + 1) + 1 = 3 * k + 4 := by omega
  rw [h35] at hA
  rw [h34] at hB
  change (2 * ((k + 1 : ℕ) : ℤ) + 3) * (a (2 * (k + 1) + 1) : ℤ) =
    3 * (2 * ((k + 1 : ℕ) : ℤ) + 2) * C3 at hA
  change (((k + 1 : ℕ) : ℤ) + 1) * (a (2 * (k + 1)) : ℤ) =
    (2 * ((k + 1 : ℕ) : ℤ) + 1) * C2 at hB
  change (2 * (k : ℤ) + 3) * (a (2 * k + 1) : ℤ) =
    3 * (2 * (k : ℤ) + 2) * C0 at hC
  push_cast at hA hB ⊢
  have hA' : (2 * (k : ℤ) + 5) * (a (2 * (k + 1) + 1) : ℤ) = 3 * (2 * (k : ℤ) + 4) * C3 := by
    linarith
  have hB' : ((k : ℤ) + 2) * (a (2 * (k + 1)) : ℤ) = (2 * (k : ℤ) + 3) * C2 := by linarith
  have hnz : (2 * (k : ℤ) + 5) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) ≠ 0 := by positivity
  apply mul_left_cancel₀ hnz
  rw [mul_zero]
  have hcomb :
      (2 * (k : ℤ) + 5) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) *
        (4 * (2 * ((k : ℤ) + 1) + 1) * (2 * ((k : ℤ) + 1) + 1 - 1) *
            (3 * (2 * ((k : ℤ) + 1) + 1) + 2) * (2 * ((k : ℤ) + 1) + 1 + 2) *
            (a (2 * (k + 1) + 1) : ℤ) -
          36 * (2 * ((k : ℤ) + 1) + 1 - 1) * (2 * ((k : ℤ) + 1) + 1 + 1) *
            (a (2 * (k + 1)) : ℤ) -
          3 * (2 * ((k : ℤ) + 1) + 1) * (3 * (2 * ((k : ℤ) + 1) + 1) + 5) *
            (3 * (2 * ((k : ℤ) + 1) + 1) - 1) * (3 * (2 * ((k : ℤ) + 1) + 1) - 2) *
            (a (2 * k + 1) : ℤ)) =
      4 * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * (6 * (k : ℤ) + 11) * (2 * (k : ℤ) + 5) *
          ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * ((2 * (k : ℤ) + 5) * (a (2 * (k + 1) + 1) : ℤ)) -
        36 * (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 3) *
          (((k : ℤ) + 2) * (a (2 * (k + 1)) : ℤ)) -
        3 * (2 * (k : ℤ) + 3) * (6 * (k : ℤ) + 14) * (6 * (k : ℤ) + 8) * (6 * (k : ℤ) + 7) *
          (2 * (k : ℤ) + 5) * ((k : ℤ) + 2) * ((2 * (k : ℤ) + 3) * (a (2 * k + 1) : ℤ)) := by
    ring
  rw [hcomb, hA', hB', hC]
  have hC2 : ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * C2 =
      (3 * (k : ℤ) + 4) * (3 * (k : ℤ) + 3) * C0 := by
    calc ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * C2
        = (2 * (k : ℤ) + 3) * (((k : ℤ) + 1) * C2) := by ring
      _ = (2 * (k : ℤ) + 3) * ((3 * (k : ℤ) + 4) * C1) := by rw [r2]
      _ = (3 * (k : ℤ) + 4) * ((2 * (k : ℤ) + 3) * C1) := by ring
      _ = (3 * (k : ℤ) + 4) * ((3 * (k : ℤ) + 3) * C0) := by rw [r1]
      _ = (3 * (k : ℤ) + 4) * (3 * (k : ℤ) + 3) * C0 := by ring
  have hnz2 : ((k : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hnz2
  rw [mul_zero]
  have hfinal :
      ((k : ℤ) + 1) *
        (4 * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * (6 * (k : ℤ) + 11) * (2 * (k : ℤ) + 5) *
            ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * (3 * (2 * (k : ℤ) + 4) * C3) -
          36 * (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 3) *
            ((2 * (k : ℤ) + 3) * C2) -
          3 * (2 * (k : ℤ) + 3) * (6 * (k : ℤ) + 14) * (6 * (k : ℤ) + 8) * (6 * (k : ℤ) + 7) *
            (2 * (k : ℤ) + 5) * ((k : ℤ) + 2) * (3 * (2 * (k : ℤ) + 2) * C0)) =
      12 * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * (6 * (k : ℤ) + 11) * (2 * (k : ℤ) + 5) *
          ((k : ℤ) + 2) * ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * ((2 * (k : ℤ) + 4) * C3) -
        36 * (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 3) *
          (((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * C2) -
        9 * ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * (6 * (k : ℤ) + 14) * (6 * (k : ℤ) + 8) *
          (6 * (k : ℤ) + 7) * (2 * (k : ℤ) + 5) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 2) * C0 := by
    ring
  rw [hfinal, r3]
  have hfinal2 :
      12 * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * (6 * (k : ℤ) + 11) * (2 * (k : ℤ) + 5) *
          ((k : ℤ) + 2) * ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * ((3 * (k : ℤ) + 5) * C2) -
        36 * (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 3) *
          (((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * C2) -
        9 * ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * (6 * (k : ℤ) + 14) * (6 * (k : ℤ) + 8) *
          (6 * (k : ℤ) + 7) * (2 * (k : ℤ) + 5) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 2) * C0 =
      12 * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 2) * (6 * (k : ℤ) + 11) * (2 * (k : ℤ) + 5) *
          ((k : ℤ) + 2) * (3 * (k : ℤ) + 5) * (((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * C2) -
        36 * (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 3) *
          (((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * C2) -
        9 * ((k : ℤ) + 1) * (2 * (k : ℤ) + 3) * (6 * (k : ℤ) + 14) * (6 * (k : ℤ) + 8) *
          (6 * (k : ℤ) + 7) * (2 * (k : ℤ) + 5) * ((k : ℤ) + 2) * (2 * (k : ℤ) + 2) * C0 := by
    ring
  rw [hfinal2, hC2]
  ring

end OMA.P_oeis_a099576

theorem OMA.solution : type_of% @OMA.S_oeis_a099576.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by omega
    simpa [Nat.cast_mul, Nat.cast_ofNat] using OMA.P_oeis_a099576.recurrence_even m hm
  · have hm : 1 ≤ m := by omega
    have hsub1 : 2 * m + 1 - 1 = 2 * m := by omega
    have hsub2 : 2 * m + 1 - 2 = 2 * m - 1 := by omega
    rw [hsub1, hsub2]
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      OMA.P_oeis_a099576.recurrence_odd m hm
