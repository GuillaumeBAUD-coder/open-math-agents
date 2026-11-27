import OMAStatements.S_oeis_a143310

theorem OMA.solution : type_of% @OMA.S_oeis_a143310.main := by
  intro n k hk hkn
  unfold OMA.S_oeis_a143310.T OMA.S_oeis_a143310.A000012 OMA.S_oeis_a143310.A127446
  have hL : ∀ j ∈ Finset.Icc 1 n, ((if j ≤ n then 1 else 0) *
      (if 1 ≤ k ∧ k ≤ j ∧ k ∣ j then j else 0) : ℕ) = if k ∣ j then j else 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [if_pos hj.2, one_mul]
    by_cases h : k ∣ j
    · rw [if_pos h, if_pos ⟨hk, Nat.le_of_dvd (by omega) h, h⟩]
    · rw [if_neg h, if_neg (fun h2 => h h2.2.2)]
  rw [Finset.sum_congr rfl hL, ← Finset.sum_filter, ← Finset.sum_filter]
  have himg : (Finset.Icc 1 n).filter (fun j => k ∣ j) =
      ((Finset.Icc 1 n).filter (fun i => i * k ≤ n)).image (· * k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, c, rfl⟩
      refine ⟨c, ⟨⟨?_, ?_⟩, ?_⟩, mul_comm c k⟩
      · rcases c with _ | c
        · simp at h1
        · omega
      · nlinarith
      · rw [mul_comm]; exact h2
    · rintro ⟨i, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      exact ⟨⟨by nlinarith, h3⟩, Dvd.intro_left i rfl⟩
  rw [himg, Finset.sum_image]
  intro a _ b _ h
  exact Nat.eq_of_mul_eq_mul_right hk h
