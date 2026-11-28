import OMAStatements.S_oeis_a180319

/-- Pairs in `[0, m)²` at distance exactly `d`. -/
def a180319_R (m d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m ×ˢ Finset.range m).filter (fun p => p.1 + d = p.2 ∨ p.2 + d = p.1)

lemma a180319_card_R (m d : ℕ) (hd : 0 < d) : (a180319_R m d).card = 2 * (m - d) := by
  unfold a180319_R
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  · have h1 : ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => p.1 + d = p.2)).card
        = m - d := by
      rw [← Finset.card_range (m - d)]
      symm
      apply Finset.card_nbij' (fun i => (i, i + d)) (fun p => p.1)
      · intro i hi; simp at hi ⊢; omega
      · intro p hp; simp at hp ⊢; omega
      · intro i hi; simp
      · intro p hp; simp at hp ⊢; ext <;> simp; omega
    have h2 : ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => p.2 + d = p.1)).card
        = m - d := by
      rw [← Finset.card_range (m - d)]
      symm
      apply Finset.card_nbij' (fun i => (i + d, i)) (fun p => p.2)
      · intro i hi; simp at hi ⊢; omega
      · intro p hp; simp at hp ⊢; omega
      · intro i hi; simp
      · intro p hp; simp at hp ⊢; ext <;> simp; omega
    rw [h1, h2]; ring
  · rw [Finset.disjoint_left]
    intro p hp hq
    simp at hp hq
    omega

lemma a180319_count (n : ℕ) :
    OMA.S_oeis_a180319.a n = 2 * (n - 1) * (2 * (2 * n - 2)) + 2 * (n - 2) * (2 * (2 * n - 1)) := by
  have hT : OMA.S_oeis_a180319.a n =
      ((a180319_R n 1 ×ˢ a180319_R (2 * n) 2) ∪ (a180319_R n 2 ×ˢ a180319_R (2 * n) 1)).card := by
    unfold OMA.S_oeis_a180319.a OMA.S_oeis_a180319.board
    apply Finset.card_nbij' (fun pq => ((pq.1.1, pq.2.1), (pq.1.2, pq.2.2)))
      (fun pq => ((pq.1.1, pq.2.1), (pq.1.2, pq.2.2)))
    · intro pq hpq
      simp [a180319_R] at hpq ⊢
      omega
    · intro pq hpq
      simp [a180319_R] at hpq ⊢
      omega
    · intro pq _; rfl
    · intro pq _; rfl
  have hdisj : Disjoint (a180319_R n 1 ×ˢ a180319_R (2 * n) 2) (a180319_R n 2 ×ˢ a180319_R (2 * n) 1) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp [a180319_R] at hp hq
    omega
  rw [hT, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    a180319_card_R _ _ (by norm_num), a180319_card_R _ _ (by norm_num),
    a180319_card_R _ _ (by norm_num), a180319_card_R _ _ (by norm_num)]

theorem OMA.solution : type_of% @OMA.S_oeis_a180319.main := by
  have hc : ∀ n : ℕ, 1 < n → (OMA.S_oeis_a180319.a n : ℤ) = 4 * (4 - 9 * n + 4 * n ^ 2) := by
    intro n hn
    rw [a180319_count]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, show 2 * (m + 2) - 2 = 2 * m + 2 by omega,
      show m + 2 - 2 = m by omega, show 2 * (m + 2) - 1 = 2 * m + 3 by omega]
    push_cast
    ring
  refine ⟨hc, ?_, ?_⟩
  · intro n hn
    rw [hc n (by omega), hc (n - 1) (by omega), hc (n - 2) (by omega), hc (n - 3) (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega]
    push_cast
    ring
  · have hq : ∀ n : ℕ, 1 < n → (OMA.S_oeis_a180319.a n : ℚ) = 4 * (4 - 9 * n + 4 * n ^ 2) := by
      intro n hn
      have := hc n hn
      exact_mod_cast this
    have h1 : OMA.S_oeis_a180319.a 1 = 0 := by rw [a180319_count]
    ext m
    have e3 : (1 - PowerSeries.X : PowerSeries ℚ) ^ 3 =
        1 - 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by ring
    rw [e3]
    set f : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a180319.a n : ℚ) with hf
    rw [show PowerSeries.mk f * (1 - 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
        = PowerSeries.mk f - PowerSeries.C (3 : ℚ) * (PowerSeries.mk f * PowerSeries.X ^ 1)
          + PowerSeries.C (3 : ℚ) * (PowerSeries.mk f * PowerSeries.X ^ 2)
          - PowerSeries.mk f * PowerSeries.X ^ 3 by simp only [map_ofNat]; ring]
    rw [show (4 : PowerSeries ℚ) * PowerSeries.X ^ 2 * (2 + 7 * PowerSeries.X - PowerSeries.X ^ 2)
        = PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (28 : ℚ) * PowerSeries.X ^ 3
          - PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 4 by simp only [map_ofNat]; ring]
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk]
    simp only [PowerSeries.coeff_C]
    have hf0 : ∀ n : ℕ, 1 < n → f n = 4 * (4 - 9 * n + 4 * n ^ 2) := by
      intro n hn; rw [hf]; simp only [show n ≠ 0 by omega, if_false]; exact hq n hn
    have hf1 : f 1 = 0 := by rw [hf]; simp [h1]
    have hf00 : f 0 = 0 := by rw [hf]; simp
    rcases Nat.lt_or_ge m 5 with hm | hm
    · interval_cases m
      · simp [hf]
      · simp [hf00, hf1]
      · simp [hf00, hf1, hf0 2 (by norm_num)]; norm_num
      · simp [hf00, hf1, hf0 2 (by norm_num), hf0 3 (by norm_num)]; norm_num
      · simp [hf1, hf0 2 (by norm_num), hf0 3 (by norm_num), hf0 4 (by norm_num)]; norm_num
    · simp only [show 1 ≤ m by omega, show 2 ≤ m by omega, show 3 ≤ m by omega,
        show 4 ≤ m by omega, show m - 2 ≠ 0 by omega, show m - 3 ≠ 0 by omega,
        show m - 4 ≠ 0 by omega, if_true, if_false]
      rw [hf0 m (by omega), hf0 (m - 1) (by omega), hf0 (m - 2) (by omega),
        hf0 (m - 3) (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
        show k + 3 - 3 = k by omega]
      push_cast
      ring
