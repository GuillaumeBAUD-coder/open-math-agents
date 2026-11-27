import OMAStatements.S_oeis_a066839

open OMA.S_oeis_a066839

private lemma sum_arith_add (k m : ℕ) :
    (∑ i ∈ Finset.range k, (m + 2 * i)) + k = k * (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 : (∑ i ∈ Finset.range k, (m + 2 * i)) + (m + 2 * k) + (k + 1) =
        ((∑ i ∈ Finset.range k, (m + 2 * i)) + k) + (m + 2 * k + 1) := by ring
    rw [h1, ih]
    ring

private lemma sum_arith (k m : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range k, (m + 2 * i) = k * (m - 1 + k) := by
  have h := sum_arith_add k m
  have hm1 : m + k = (m - 1 + k) + 1 := by omega
  rw [hm1, mul_add, mul_one] at h
  exact Nat.add_right_cancel h

theorem OMA.solution : type_of% @OMA.S_oeis_a066839.main := by
  intro n hn
  unfold a totalParts
  refine Finset.sum_bij (fun k _ => (k, n / k + 1 - k)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Nat.mem_divisors] at hk
    obtain ⟨⟨hdvd, hn0⟩, hkk⟩ := hk
    have hkpos : 1 ≤ k := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hkle : k ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hmul : k * (n / k) = n := Nat.mul_div_cancel' hdvd
    have hkq : k ≤ n / k := by
      have : k * k ≤ k * (n / k) := by omega
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have hqle : n / k ≤ n := Nat.div_le_self n k
    have hmpos : 1 ≤ n / k + 1 - k := by omega
    have hmle : n / k + 1 - k ≤ n := by omega
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨hkpos, hkle⟩, ⟨hmpos, hmle⟩⟩, ?_⟩
    rw [sum_arith k (n / k + 1 - k) hmpos]
    have hsub : n / k + 1 - k - 1 + k = n / k := by omega
    rw [hsub, hmul]
  · intro k₁ _ k₂ _ h
    exact (Prod.mk.inj h).1
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hkpos, _⟩, ⟨hmpos, _⟩⟩, hsum⟩ := hp
    rw [sum_arith p.1 p.2 hmpos] at hsum
    refine ⟨p.1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨⟨p.2 - 1 + p.1, hsum.symm⟩, by omega⟩, ?_⟩
      calc p.1 * p.1 ≤ p.1 * (p.2 - 1 + p.1) := Nat.mul_le_mul_left p.1 (by omega)
        _ = n := hsum
    · have hdiv : n / p.1 = p.2 - 1 + p.1 := by
        rw [← hsum]
        exact Nat.mul_div_cancel_left (p.2 - 1 + p.1) (by omega)
      ext
      · rfl
      · dsimp
        omega
  · intro k _
    rfl
