import FormalConjectures.Wikipedia.RowlandSequence

/-! Rowland’s recurrence has only unit and prime increments. -/

open RowlandSequence

namespace OMA.Rowland

-- At b the sequence equals 3b. The offset j counts the unit steps since then.
def InRun (n : ℕ) : Prop :=
  ∃ b j : ℕ, 3 ≤ b ∧ n = b + j ∧ rowlandSeq n = 3 * b + j ∧
    2 * j + 1 < (2 * b - 1).minFac

lemma next_value {n : ℕ} (hn : 0 < n) :
    rowlandSeq (n + 1) = rowlandSeq n + Nat.gcd (n + 1) (rowlandSeq n) := by
  cases n with
  | zero => omega
  | succ k => rfl

lemma advance {n : ℕ} (h : InRun n) :
    InRun (n + 1) ∧ (rowlandDiff (n + 1) = 1 ∨ (rowlandDiff (n + 1)).Prime) := by
  obtain ⟨b, j, hb, rfl, ha, hj⟩ := h
  let p := (2 * b - 1).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpM : p ∣ 2 * b - 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro he
    rw [he] at hpM
    omega
  obtain ⟨u, hu⟩ := hp.odd_of_ne_two hp2
  change 2 * j + 1 < p at hj
  have hbound : 2 * j + 3 ≤ p := by omega
  let g := Nat.gcd (b + j + 1) (2 * b - 1)
  have hgN : g ∣ b + j + 1 := Nat.gcd_dvd_left _ _
  have hgM : g ∣ 2 * b - 1 := Nat.gcd_dvd_right _ _
  have hsum : (2 * b - 1) + (2 * j + 3) = (b + j + 1) + (b + j + 1) := by omega
  have hgT : g ∣ 2 * j + 3 := by
    have hh := Nat.dvd_sub (dvd_add hgN hgN) hgM
    simpa only [← hsum, Nat.add_sub_cancel_left] using hh
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgT (by omega)
  have hgle : g ≤ 2 * j + 3 := Nat.le_of_dvd (by omega) hgT
  have hnext : rowlandSeq (b + j + 1) = 3 * b + j + g := by
    rw [next_value (by omega), ha]
    congr 1
    change Nat.gcd (b + j + 1) (3 * b + j) = Nat.gcd _ _
    rw [show 3 * b + j = (2 * b - 1) + (b + j + 1) by omega]
    simp
  have hdiff : rowlandDiff (b + j + 1) = g := by simp [rowlandDiff, hnext, ha]
  rw [hdiff]
  by_cases hlast : 2 * j + 3 = p
  · have hpN : p ∣ b + j + 1 := by
      have hh : p ∣ 2 * (b + j + 1) := by
        rw [two_mul, ← hsum, hlast]
        exact dvd_add hpM dvd_rfl
      rcases hp.dvd_mul.mp hh with htwo | hN
      · have := Nat.le_of_dvd (by decide : 0 < 2) htwo
        have := hp.two_le
        omega
      · exact hN
    have hp_le : p ≤ g := Nat.le_of_dvd hgpos (Nat.dvd_gcd hpN hpM)
    have hgp : g = p := by omega
    refine ⟨⟨b + j + 1, 0, by omega, by omega, by omega, ?_⟩, Or.inr (by simpa only [hgp] using hp)⟩
    exact (Nat.minFac_prime (by omega : 2 * (b + j + 1) - 1 ≠ 1)).one_lt
  · have hg1 : g = 1 := by
      by_contra hne
      have hmin : p ≤ g := Nat.minFac_le_of_dvd (by omega) hgM
      omega
    exact ⟨⟨b, j + 1, hb, by omega, by omega, by change 2 * (j + 1) + 1 < p; omega⟩,
      Or.inl hg1⟩

lemma inRun_from_three (k : ℕ) : InRun (3 + k) := by
  induction k with
  | zero => exact ⟨3, 0, by decide, rfl, by decide, by norm_num⟩
  | succ k ih => exact (advance ih).1

end OMA.Rowland

theorem OMA.solution : type_of% @RowlandSequence.rowland_diff_eq_one_or_prime := by
  intro n hn
  by_cases hsmall : n ≤ 3
  · interval_cases n <;> decide
  · have h := (OMA.Rowland.advance (OMA.Rowland.inRun_from_three (n - 4))).2
    rwa [show 3 + (n - 4) + 1 = n by omega] at h
