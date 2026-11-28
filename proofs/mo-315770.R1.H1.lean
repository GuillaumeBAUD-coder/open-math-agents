import OMAReductions.R_mo_315770_R1

-- Step mo-315770.R1.H1: hypothesis H1 of reduction mo-315770.R1
-- Credit: @sovrana

theorem sum_form (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, (1 : ℚ) / ((d : ℚ) + 1) = ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / ((p : ℚ) ^ i + 1) := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp

theorem upper (p : ℕ) (hp : 2 ≤ p) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / ((p : ℚ) ^ i + 1)
      ≤ 1 / 2 + 1 / ((p : ℚ) - 1) - (1 / ((p : ℚ) - 1)) * (1 / (p : ℚ)) ^ k := by
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hp0 : (0 : ℚ) < p := by linarith
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 : (1 : ℚ) / ((p : ℚ) ^ (k + 1) + 1) ≤ (1 / (p : ℚ)) ^ (k + 1) := by
      rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
      linarith
    have h2 : (1 / ((p : ℚ) - 1)) * (1 / (p : ℚ)) ^ k - (1 / ((p : ℚ) - 1)) * (1 / (p : ℚ)) ^ (k + 1)
        = (1 / (p : ℚ)) ^ (k + 1) := by
      have hp0' : (p : ℚ) ≠ 0 := hp0.ne'
      have hp1' : (p : ℚ) - 1 ≠ 0 := hp1.ne'
      rw [pow_succ]
      field_simp
    linarith

theorem sol : ∀ p k : ℕ, p.Prime → ∀ z : ℤ, ∑ d ∈ (p ^ k).divisors, (1 : ℚ) / ((d : ℚ) + 1) ≠ z := by
  intro p k hp z hz
  rw [sum_form p k hp] at hz
  have hp2 := hp.two_le
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp2
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hup := upper p hp2 k
  have hpos : (0 : ℚ) < (1 / (p : ℚ)) ^ k := by positivity
  have hlt : ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / ((p : ℚ) ^ i + 1) < 1 / 2 + 1 / ((p : ℚ) - 1) := by
    have : 0 < (1 / ((p : ℚ) - 1)) * (1 / (p : ℚ)) ^ k := by positivity
    linarith
  have hgt : (0 : ℚ) < ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / ((p : ℚ) ^ i + 1) := by
    apply Finset.sum_pos
    · intro i _; positivity
    · exact ⟨0, by simp⟩
  rcases Nat.eq_or_lt_of_le hp2 with h2 | h3
  · -- p = 2
    subst h2
    have hlt' : ∑ i ∈ Finset.range (k + 1), (1 : ℚ) / (((2 : ℕ) : ℚ) ^ i + 1) < 3 / 2 := by
      norm_num at hlt ⊢; linarith
    have hz1 : z = 1 := by
      have a : (z : ℚ) < 2 := by linarith
      have b : (0 : ℚ) < z := by linarith
      have a' : z < 2 := by exact_mod_cast a
      have b' : 0 < z := by exact_mod_cast b
      omega
    subst hz1
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
    · norm_num at hz
    · norm_num [Finset.sum_range_succ] at hz
    · have hsub : Finset.range 3 ⊆ Finset.range (k + 1) := Finset.range_subset_range.2 (by omega)
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (1 : ℚ) / (((2 : ℕ) : ℚ) ^ i + 1)) hsub
        (fun i _ _ => by positivity)
      norm_num [Finset.sum_range_succ] at this hz
      linarith
  · have hp3 : (3 : ℚ) ≤ p := by exact_mod_cast h3
    have hle : 1 / ((p : ℚ) - 1) ≤ 1 / 2 := by
      rw [one_div_le_one_div hp1 (by norm_num)]; linarith
    have hz0 : (0 : ℚ) < z := by linarith
    have hz1 : (z : ℚ) < 1 := by linarith
    have a : 0 < z := by exact_mod_cast hz0
    have b : z < 1 := by exact_mod_cast hz1
    omega

theorem OMA.solution : OMA.R_mo_315770_R1.H1 := sol
