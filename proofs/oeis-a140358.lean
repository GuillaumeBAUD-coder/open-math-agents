import OMAStatements.S_oeis_a140358

open OMA.S_oeis_a140358

lemma OMA.t2_a140358 (k : ℕ) : 2 * t k = k * (k + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

lemma OMA.tsucc_a140358 (k : ℕ) : t (k + 1) = t k + (k + 1) := by
  have h1 := OMA.t2_a140358 k
  have h2 := OMA.t2_a140358 (k + 1)
  have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
  omega

lemma OMA.tmono_a140358 {j k : ℕ} (h : j < k) : t j < t k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [OMA.tsucc_a140358]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · have := ih h; omega
    · subst h; omega

lemma OMA.nec_a140358 (ε : ℕ → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (k : ℕ) :
    -(t k : ℤ) ≤ ∑ i ∈ Finset.Icc 1 k, ε i * (i : ℤ) ∧
    ∑ i ∈ Finset.Icc 1 k, ε i * (i : ℤ) ≤ t k ∧
    (∑ i ∈ Finset.Icc 1 k, ε i * (i : ℤ) - t k) % 2 = 0 := by
  induction k with
  | zero => simp [t]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), OMA.tsucc_a140358]
    push_cast
    rcases hε (k + 1) with h | h <;> rw [h] <;> omega

lemma OMA.suff_a140358 (k : ℕ) : ∀ n : ℤ, -(t k : ℤ) ≤ n → n ≤ t k → (n - t k) % 2 = 0 →
    ∃ ε : ℕ → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ n = ∑ i ∈ Finset.Icc 1 k, ε i * (i : ℤ) := by
  induction k with
  | zero =>
    intro n h1 h2 _
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    simp [t] at h1 h2 ⊢; omega
  | succ k ih =>
    intro n h1 h2 h3
    rw [OMA.tsucc_a140358] at h1 h2 h3
    push_cast at h1 h2 h3
    have hk : k = 0 ∨ k = 1 ∨ k + 1 ≤ t k := by
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · right; right
        have := OMA.t2_a140358 k
        nlinarith
    have ht0 : t 0 = 0 := rfl
    have ht1 : t 1 = 1 := rfl
    obtain ⟨s, hs, m, hm1, hm2, hm3, hn⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∃ m : ℤ,
        -(t k : ℤ) ≤ m ∧ m ≤ t k ∧ (m - t k) % 2 = 0 ∧ n = m + s * ((k : ℤ) + 1) := by
      rcases le_or_gt 0 n with h | h
      · refine ⟨1, Or.inl rfl, n - (k + 1), ?_, ?_, ?_, ?_⟩
        · rcases hk with hk | hk | hk
          · subst hk; rw [ht0] at h1 h2 h3 ⊢; omega
          · subst hk; rw [ht1] at h1 h2 h3 ⊢; omega
          · omega
        · omega
        · omega
        · ring
      · refine ⟨-1, Or.inr rfl, n + (k + 1), ?_, ?_, ?_, ?_⟩
        · omega
        · rcases hk with hk | hk | hk
          · subst hk; rw [ht0] at h1 h2 h3 ⊢; omega
          · subst hk; rw [ht1] at h1 h2 h3 ⊢; omega
          · omega
        · omega
        · ring
    obtain ⟨ε, hε, he⟩ := ih m hm1 hm2 hm3
    refine ⟨fun i => if i = k + 1 then s else ε i, fun i => ?_, ?_⟩
    · dsimp only; split_ifs
      · exact hs
      · exact hε i
    · rw [Finset.sum_Icc_succ_top (by omega), hn, he]
      dsimp only
      rw [if_pos rfl]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Icc] at hi
        rw [if_neg (by omega)]

lemma OMA.rep_a140358 (n k : ℕ) : k ∈ {k : ℕ | ∃ ε : ℕ → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    (n : ℤ) = ∑ i ∈ Finset.Icc 1 k, ε i * (i : ℤ)} ↔ n ≤ t k ∧ (t k - n) % 2 = 0 := by
  constructor
  · rintro ⟨ε, hε, he⟩
    have := OMA.nec_a140358 ε hε k
    rw [← he] at this
    omega
  · rintro ⟨h1, h2⟩
    exact OMA.suff_a140358 k n (by omega) (by omega) (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a140358.main := by
  intro n k hn h1 h2
  have hs1 := OMA.tsucc_a140358 k
  have hs2 : t (k + 2) = t (k + 1) + (k + 2) := OMA.tsucc_a140358 (k + 1)
  have hs3 : t (k + 3) = t (k + 2) + (k + 3) := OMA.tsucc_a140358 (k + 2)
  rw [hs1] at h2
  have low : ∀ j, j < k → ¬ (n ≤ t j) := fun j hj => by
    have := OMA.tmono_a140358 hj; omega
  have key : ∀ v : ℕ, (n ≤ t v ∧ (t v - n) % 2 = 0) →
      (∀ j, k ≤ j → j < v → ¬ (n ≤ t j ∧ (t j - n) % 2 = 0)) → a n = v := by
    intro v hv hlt
    apply le_antisymm
    · exact Nat.sInf_le ((OMA.rep_a140358 n v).mpr hv)
    · apply le_csInf ⟨v, (OMA.rep_a140358 n v).mpr hv⟩
      intro j hj
      rw [OMA.rep_a140358] at hj
      by_contra hc
      rcases lt_or_ge j k with h | h
      · exact low j h hj.1
      · exact hlt j h (by omega) hj
  have j3 : ∀ j, k ≤ j → j < k + 3 → j = k ∨ j = k + 1 ∨ j = k + 2 := by omega
  simp only [Nat.odd_iff]
  split_ifs <;>
  · refine key _ ⟨by omega, by omega⟩ ?_
    intro j hj1 hj2
    rcases j3 j hj1 (by omega) with rfl | rfl | rfl <;> omega
