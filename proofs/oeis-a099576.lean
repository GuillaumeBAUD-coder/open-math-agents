import OMAStatements.S_oeis_a099576
import Mathlib
open OMA.S_oeis_a099576
open Finset

theorem hockey (n J : ℕ) : ∑ j ∈ range (J + 1), (n + j).choose j = (n + J + 1).choose J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih, show n + (J + 1) + 1 = (n + J + 1) + 1 by ring,
      Nat.choose_succ_succ (n + J + 1) J, show n + (J + 1) = n + J + 1 by ring]

theorem a_eq (n : ℕ) : a n = ∑ k ∈ range (n + 1), (n + k / 2 + 1).choose (k / 2) := by
  unfold a
  refine sum_congr rfl fun k _ => ?_
  rw [hockey]

theorem split1 (g : ℕ → ℕ) (m : ℕ) :
    ∑ k ∈ range (2 * m + 1), g (k / 2) = 2 * ∑ i ∈ range m, g i + g m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
    ring

theorem split2 (g : ℕ → ℕ) (m : ℕ) :
    ∑ k ∈ range (2 * m + 2), g (k / 2) = 2 * ∑ i ∈ range (m + 1), g i := by
  rw [sum_range_succ, split1, show (2 * m + 1) / 2 = m by omega, sum_range_succ]
  ring

theorem aE (m : ℕ) : a (2 * m + 2) = 2 * (3 * m + 4).choose m + (3 * m + 4).choose (m + 1) := by
  rw [a_eq, show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by ring,
    split1 (fun i => (2 * m + 2 + i + 1).choose i)]
  have := hockey (2 * m + 3) m
  rw [show (∑ i ∈ range (m + 1), (2 * m + 2 + i + 1).choose i) =
      ∑ i ∈ range (m + 1), (2 * m + 3 + i).choose i from
      sum_congr rfl fun i _ => by rw [show 2 * m + 2 + i + 1 = 2 * m + 3 + i by ring], this,
    show 2 * m + 3 + m + 1 = 3 * m + 4 by ring, show 2 * m + 2 + (m + 1) + 1 = 3 * m + 4 by ring]

theorem aO (m : ℕ) : a (2 * m + 1) = 2 * (3 * m + 3).choose m := by
  rw [a_eq, show 2 * m + 1 + 1 = 2 * m + 2 by ring,
    split2 (fun i => (2 * m + 1 + i + 1).choose i)]
  have := hockey (2 * m + 2) m
  rw [show (∑ i ∈ range (m + 1), (2 * m + 1 + i + 1).choose i) =
      ∑ i ∈ range (m + 1), (2 * m + 2 + i).choose i from
      sum_congr rfl fun i _ => by rw [show 2 * m + 1 + i + 1 = 2 * m + 2 + i by ring], this,
    show 2 * m + 2 + m + 1 = 3 * m + 3 by ring]

theorem cc (n k l : ℕ) (h : n = k + l) :
    ((n.choose k : ℕ) : ℚ) = (n.factorial : ℚ) / ((k.factorial : ℚ) * (l.factorial : ℚ)) := by
  subst h
  rw [Nat.cast_choose ℚ (by omega), Nat.add_sub_cancel_left]

theorem OMA.solution : type_of% @OMA.S_oeis_a099576.main := by
  show ∀ n : ℕ, 2 ≤ n →
    4 * (n : ℤ) * ((n : ℤ) - 1) * (3 * (n : ℤ) + 2) * ((n : ℤ) + 2) * (a n : ℤ) -
      36 * ((n : ℤ) - 1) * ((n : ℤ) + 1) * (a (n - 1) : ℤ) -
      3 * (n : ℤ) * (3 * (n : ℤ) + 5) * (3 * (n : ℤ) - 1) *
        (3 * (n : ℤ) - 2) * (a (n - 2) : ℤ) = 0
  intro n hn
  apply Int.cast_injective (α := ℚ)
  push_cast
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [a, Finset.sum_range_succ]; norm_num
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e1 : a (2 * (m + 1 + 1)) = 2 * (3 * m + 7).choose (m + 1) + (3 * m + 7).choose (m + 2) := by
      rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by ring, aE, show 3 * (m + 1) + 4 = 3 * m + 7 by ring]
    have e2 : a (2 * (m + 1 + 1) - 1) = 2 * (3 * m + 6).choose (m + 1) := by
      rw [show 2 * (m + 1 + 1) - 1 = 2 * (m + 1) + 1 by omega, aO, show 3 * (m + 1) + 3 = 3 * m + 6 by ring]
    have e3 : a (2 * (m + 1 + 1) - 2) = 2 * (3 * m + 4).choose m + (3 * m + 4).choose (m + 1) := by
      rw [show 2 * (m + 1 + 1) - 2 = 2 * m + 2 by omega, aE]
    rw [e1, e2, e3]
    push_cast
    rw [cc (3*m+7) (m+1) (2*m+6) (by ring), cc (3*m+7) (m+2) (2*m+5) (by ring),
      cc (3*m+6) (m+1) (2*m+5) (by ring), cc (3*m+4) m (2*m+4) (by ring),
      cc (3*m+4) (m+1) (2*m+3) (by ring)]
    simp [Nat.factorial]
    field_simp
    ring
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e1 : a (2 * (m + 1) + 1) = 2 * (3 * m + 6).choose (m + 1) := by
      rw [aO, show 3 * (m + 1) + 3 = 3 * m + 6 by ring]
    have e2 : a (2 * (m + 1) + 1 - 1) = 2 * (3 * m + 4).choose m + (3 * m + 4).choose (m + 1) := by
      rw [show 2 * (m + 1) + 1 - 1 = 2 * m + 2 by omega, aE]
    have e3 : a (2 * (m + 1) + 1 - 2) = 2 * (3 * m + 3).choose m := by
      rw [show 2 * (m + 1) + 1 - 2 = 2 * m + 1 by omega, aO]
    rw [e1, e2, e3]
    push_cast
    rw [cc (3*m+6) (m+1) (2*m+5) (by ring), cc (3*m+4) m (2*m+4) (by ring),
      cc (3*m+4) (m+1) (2*m+3) (by ring), cc (3*m+3) m (2*m+3) (by ring)]
    simp [Nat.factorial]
    field_simp
    ring
