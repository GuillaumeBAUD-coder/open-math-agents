import FormalConjectures.Wikipedia.RowlandSequence

/-! Rowland's recurrence has only unit and prime increments. -/

open RowlandSequence

theorem OMA.solution : type_of% @RowlandSequence.rowland_diff_eq_one_or_prime := by
  intro n hn
  by_cases hs : n ≤ 3
  · interval_cases n <;> decide
  have step : ∀ k, (∃ b j, 3 ≤ b ∧ 3 + k = b + j ∧ rowlandSeq (3 + k) = 3 * b + j ∧
      2 * j + 1 < (2 * b - 1).minFac) ∧ (k = 0 ∨ rowlandDiff (3 + k) = 1 ∨ (rowlandDiff (3 + k)).Prime) := by
    intro k; induction k with
    | zero => exact ⟨⟨3, 0, by decide, rfl, by decide, by norm_num⟩, Or.inl rfl⟩
    | succ k ih =>
      obtain ⟨b, j, hb, hbj, ha, hj⟩ := ih.1
      let p := (2 * b - 1).minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpM : p ∣ 2 * b - 1 := Nat.minFac_dvd _
      obtain ⟨_, _⟩ := hp.odd_of_ne_two fun h => by rw [h] at hpM; omega
      let g := Nat.gcd (b + j + 1) (2 * b - 1)
      have hgM : g ∣ 2 * b - 1 := Nat.gcd_dvd_right _ _
      have hsum : (2 * b - 1) + (2 * j + 3) = (b + j + 1) + (b + j + 1) := by omega
      have hgT : g ∣ 2 * j + 3 :=
        (Nat.dvd_add_right hgM).1 (hsum ▸ dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
      have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgT (by omega)
      have hgle : g ≤ 2 * j + 3 := Nat.le_of_dvd (by omega) hgT
      have hnext : rowlandSeq (3 + (k + 1)) = 3 * b + j + g := by
        rw [show 3 + (k + 1) = k + 2 + 2 by omega, rowlandSeq, show k + 2 + 1 = 3 + k by omega, ha,
          show k + 2 + 2 = b + j + 1 by omega, show 3 * b + j = (2 * b - 1) + (b + j + 1) by omega]
        simp [g]
      have hdiff : rowlandDiff (3 + (k + 1)) = g := by
        simp [rowlandDiff, hnext, ha]
      rw [hdiff]
      by_cases hlast : 2 * j + 3 = p
      · have hpN : p ∣ b + j + 1 :=
          (hp.dvd_mul.mp (by rw [two_mul, ← hsum, hlast]; exact dvd_add hpM dvd_rfl)).resolve_left
            fun h2 => by have := Nat.le_of_dvd two_pos h2; have := hp.two_le; omega
        have hgp : g = p := le_antisymm (by omega) (Nat.le_of_dvd hgpos (Nat.dvd_gcd hpN hpM))
        exact ⟨⟨b + j + 1, 0, by omega, by omega, by omega,
          (Nat.minFac_prime (by omega : 2 * (b + j + 1) - 1 ≠ 1)).one_lt⟩, Or.inr (Or.inr (hgp ▸ hp))⟩
      · have hg1 : g = 1 := by
          by_contra; have := Nat.minFac_le_of_dvd (by omega) hgM; omega
        exact ⟨⟨b, j + 1, hb, by omega, by omega, by change 2 * (j + 1) + 1 < p; omega⟩, Or.inr (Or.inl hg1)⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 + k := ⟨n - 3, by omega⟩
  exact (step k).2.resolve_left (by omega)
