import OMAStatements.S_oeis_a387064

open Finset

theorem OMA.solution : type_of% @OMA.S_oeis_a387064.main := by
  intro p k hp hk
  have : Fact p.Prime := ⟨hp⟩
  have early {r j : ℕ} (hr : r < p ^ k) (hj : j ≤ r) : ¬ p ^ k ∣ r.choose j := by
    rw [Nat.pow_dvd_iff_le_padicValNat hp.ne_one (Nat.choose_ne_zero hj),
      padicValNat_choose hj (Nat.log_lt_of_lt_pow' (by omega : k ≠ 0) hr)]
    have h := Finset.card_filter_le (Finset.Ico 1 k)
      (fun i => p ^ i ≤ j % p ^ i + (r - j) % p ^ i)
    rw [Nat.card_Ico] at h
    omega
  have lastRow {j : ℕ} (hj : j ≤ p ^ k) : p ^ k ∣ (p ^ k).choose j ↔ ¬ p ∣ j := by
    constructor
    · intro hd hjp
      have hlog : Nat.log p (p ^ k) < k + 1 := by rw [Nat.log_pow hp.one_lt]; omega
      rw [Nat.pow_dvd_iff_le_padicValNat hp.ne_one (Nat.choose_ne_zero hj),
        padicValNat_choose hj hlog] at hd
      have sub : ((Ico 1 (k + 1)).filter fun i =>
          p ^ i ≤ j % p ^ i + (p ^ k - j) % p ^ i) ⊆ Ico 2 (k + 1) := by
        intro i hi
        obtain ⟨hi, hc⟩ := mem_filter.mp hi
        obtain ⟨hl, hu⟩ := mem_Ico.mp hi
        refine mem_Ico.mpr ⟨?_, hu⟩
        by_contra! h
        have : i = 1 := by omega
        subst i
        simp only [pow_one, Nat.mod_eq_zero_of_dvd hjp, zero_add] at hc
        exact (Nat.mod_lt _ hp.pos).not_ge hc
      have hc := card_le_card sub
      rw [Nat.card_Ico] at hc
      omega
    · intro h
      have cop := (hp.coprime_pow_of_not_dvd (m := k) h).symm
      apply cop.dvd_of_dvd_mul_right
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by rintro rfl; exact h (dvd_zero _))
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero k hp.ne_zero)
      rw [hr, ← Nat.add_one_mul_choose_eq]
      exact dvd_mul_right _ _
  unfold OMA.S_oeis_a387064.a
  rw [sum_range_succ]
  have lower : ∀ r ∈ range (p ^ k),
      ((range (r + 1)).filter fun j => p ^ k ∣ r.choose j).card = 0 := by
    intro r hr
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro j hj
    exact early (mem_range.mp hr) (by simpa using mem_range.mp hj)
  rw [sum_eq_zero lower, zero_add]
  have hset : ((range (p ^ k + 1)).filter fun j => p ^ k ∣ (p ^ k).choose j) =
      ((range (p ^ k)).filter fun j => (p ^ k).Coprime j) := by
    ext j
    simp only [mem_filter, mem_range, Nat.lt_succ_iff, Nat.coprime_pow_left_iff hk,
      hp.coprime_iff_not_dvd]
    constructor
    · rintro ⟨hj, hd⟩
      have h := (lastRow hj).mp hd
      refine ⟨lt_of_le_of_ne hj ?_, h⟩
      rintro rfl
      exact h (dvd_pow_self p (by omega))
    · rintro ⟨hj, h⟩
      exact ⟨hj.le, (lastRow hj.le).mpr h⟩
  rw [hset, ← Nat.totient, Nat.totient_prime_pow hp hk, mul_comm]
