import OMAStatements.S_oeis_a376354
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

open OMA.S_oeis_a376354

namespace OMA.S_oeis_a376354.Proof

private theorem triangular_succ (k : ℕ) : triangular (k + 1) = triangular k + (k + 1) := by
  unfold triangular
  have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
  rw [h]
  omega

private theorem descend_zero (k : ℕ) : descend 0 k = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | k
    · rfl
    · rfl
    · simpa only [descend, Nat.zero_mod] using ih (k + 1) (by omega)

private theorem descend_bound (n k : ℕ) (hk : 2 ≤ k) : descend n k < 3 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rcases k with _ | _ | k
    · omega
    · simpa [descend, triangular] using Nat.mod_lt n (by decide : 0 < 3)
    · exact ih _ (by omega)

private theorem descend_step (n k : ℕ) :
    descend (n + 1) k = 0 ∨ descend (n + 1) k = descend n k + 1 := by
  induction k generalizing n with
  | zero => exact Or.inr rfl
  | succ k ih =>
    rcases k with _ | k
    · exact Or.inr rfl
    · have hpos : 1 < triangular (k + 2) := by
        have h₀ : 1 ≤ k + 1 := by omega
        rw [show k + 2 = (k + 1) + 1 from rfl, triangular_succ]
        omega
      simp only [descend]
      have hOne : 1 % triangular (k + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      by_cases h : n % triangular (k + 2) + 1 < triangular (k + 2)
      · rw [Nat.add_mod_of_add_mod_lt (by rwa [hOne]) , hOne]
        exact ih _
      · have hwrap : n % triangular (k + 2) + 1 = triangular (k + 2) := by
          have := Nat.mod_lt n (by omega : 0 < triangular (k + 2))
          omega
        left
        rw [Nat.add_mod n 1, hOne, hwrap, Nat.mod_self, descend_zero]

private theorem start_above (n : ℕ) : n < triangular (Nat.sqrt (2 * n) + 2) := by
  have h : 2 * n < (Nat.sqrt (2 * n) + 1) ^ 2 := Nat.lt_succ_sqrt' (2 * n)
  have h' : (Nat.sqrt (2 * n) + 1) ^ 2 + 1 ≤
      (Nat.sqrt (2 * n) + 2) * (Nat.sqrt (2 * n) + 2 + 1) := by nlinarith
  unfold triangular
  omega

private theorem descend_pad (n k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l)
    (hn : n < triangular (k + 1)) : descend n l = descend n k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    have hmono (a b : ℕ) (h : a ≤ b) : triangular a ≤ triangular b := by
      induction b, h using Nat.le_induction with
      | base => rfl
      | succ b hab ih =>
        rw [triangular_succ]
        omega
    have hnl := hn.trans_le (hmono (k + 1) (l + 1) (by omega))
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    simpa only [descend, Nat.mod_eq_of_lt hnl] using ih

private theorem digit_lt (n : ℕ) : digit n < 3 := by
  by_cases h : 0 < n
  · apply descend_bound
    have := Nat.sqrt_pos.2 (show 0 < 2 * n by omega)
    omega
  · have hn : n = 0 := by omega
    subst n
    decide

private theorem digit_step (n : ℕ) :
    digit (n + 1) = 0 ∨ digit (n + 1) = digit n + 1 := by
  unfold digit
  rw [← descend_pad n (Nat.sqrt (2 * n) + 1) (Nat.sqrt (2 * (n + 1)) + 1)]
  · exact descend_step _ _
  · omega
  · exact Nat.succ_le_succ (Nat.sqrt_le_sqrt (by omega))
  · exact start_above n

private theorem small_gap (a b : ℕ) (h : Consecutive 0 a b) : b - a ≤ 3 := by
  obtain ⟨_, hab, ha, _, hmid⟩ := h
  by_contra hgap
  have hn (j : ℕ) (hj : 0 < j) (hj' : j ≤ 3) : digit (a + j) ≠ 0 :=
    hmid _ (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
  have h1 := (digit_step a).resolve_left (hn 1 (by decide) (by decide))
  have h2 := (digit_step (a + 1)).resolve_left (hn 2 (by decide) (by decide))
  have h3 := (digit_step (a + 2)).resolve_left (hn 3 (by decide) (by decide))
  have hb := digit_lt (a + 3)
  have h3' : digit (a + 3) = digit (a + 2) + 1 := h3
  change digit (a + 2) = digit (a + 1) + 1 at h2
  omega

end OMA.S_oeis_a376354.Proof

open OMA.S_oeis_a376354.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a376354.main := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, h, rfl⟩
    have := small_gap a b h
    have := h.2.1
    omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨9, 10, by unfold Consecutive; decide +kernel, rfl⟩
    · exact ⟨13, 15, by unfold Consecutive; decide +kernel, rfl⟩
    · exact ⟨3, 6, by unfold Consecutive; decide +kernel, rfl⟩
