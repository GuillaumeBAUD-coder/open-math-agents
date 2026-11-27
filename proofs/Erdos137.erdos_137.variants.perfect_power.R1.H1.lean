import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

open Finset

lemma erdos137_power_of_factorization_dvd (a l : ℕ) (ha : a ≠ 0)
    (h : ∀ p, l ∣ a.factorization p) : ∃ u : ℕ, u ^ l = a := by
  refine ⟨∏ p ∈ a.factorization.support, p ^ (a.factorization p / l), ?_⟩
  rw [← Finset.prod_pow]
  calc
    (∏ p ∈ a.factorization.support, (p ^ (a.factorization p / l)) ^ l) =
        ∏ p ∈ a.factorization.support, p ^ a.factorization p := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← pow_mul, Nat.div_mul_cancel (h p)]
    _ = a := Nat.prod_factorization_pow_eq_self ha

lemma erdos137_gap_between_powers (a : ℕ) (ha : 0 < a) (r : ℕ) :
    a ^ (r + 2) + 2 ≤ (a + 1) ^ (r + 2) := by
  induction r with
  | zero =>
    simp only [Nat.zero_add]
    nlinarith
  | succ r ih =>
    rw [show r.succ + 2 = (r + 2) + 1 by omega,
      pow_succ a (r + 2), pow_succ (a + 1) (r + 2)]
    apply le_trans ?_ (Nat.mul_le_mul_right (a + 1) ih)
    have hScale := Nat.mul_le_mul_left (a ^ (r + 2)) (show a ≤ a + 1 by omega)
    rw [Nat.add_mul]
    omega

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  intro n x l hl hPower
  have hInterval : Ioc n (n + 2) = {n + 1, n + 2} := by
    ext m
    simp only [mem_Ioc, mem_insert, mem_singleton]
    omega
  have hMul : (n + 1) * (n + 2) = x ^ l := by
    simpa [hInterval, Finset.prod_insert, show n + 1 ≠ n + 2 by omega] using hPower
  have hLeftNonzero : n + 1 ≠ 0 := by omega
  have hRightNonzero : n + 2 ≠ 0 := by omega
  have hFac (p : ℕ) : l ∣ (n + 1).factorization p + (n + 2).factorization p := by
    have hEq := congrArg (fun m : ℕ => m.factorization p) hMul
    rw [Nat.factorization_mul hLeftNonzero hRightNonzero, Nat.factorization_pow] at hEq
    exact ⟨x.factorization p, hEq⟩
  have hZero (p : ℕ) : (n + 1).factorization p = 0 ∨ (n + 2).factorization p = 0 := by
    by_cases hp : p.Prime
    · by_cases hLeft : p ∣ n + 1
      · right
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hRight
        have hOne := Nat.dvd_sub hRight hLeft
        rw [show n + 2 - (n + 1) = 1 by omega] at hOne
        exact hp.ne_one (Nat.dvd_one.mp hOne)
      · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hLeft)
    · exact Or.inl (Nat.factorization_eq_zero_of_not_prime _ hp)
  obtain ⟨u, hu⟩ := erdos137_power_of_factorization_dvd (n + 1) l (by omega) (by
    intro p
    rcases hZero p with h | h
    · simp [h]
    · simpa [h] using hFac p)
  obtain ⟨v, hv⟩ := erdos137_power_of_factorization_dvd (n + 2) l (by omega) (by
    intro p
    rcases hZero p with h | h
    · simpa [h] using hFac p
    · simp [h])
  have hExp : l ≠ 0 := by omega
  have hPos : 0 < u := by
    by_contra! h
    have h' : u = 0 := by omega
    rw [h', zero_pow hExp] at hu
    omega
  have hUV : u < v := (Nat.pow_lt_pow_iff_left hExp).mp (by omega)
  have hMon : (u + 1) ^ l ≤ v ^ l :=
    (Nat.pow_le_pow_iff_left hExp).2 (by omega)
  have hGap := erdos137_gap_between_powers u hPos (l - 2)
  rw [show l - 2 + 2 = l by omega] at hGap
  omega
