import OMAStatements.S_oeis_a055246
import Mathlib

open OMA.S_oeis_a055246

namespace OMA.P_oeis_a055246

def v (m : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 m)

theorem v_even (m : ℕ) : v (2 * m) = 3 * v m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [v]
  · unfold v
    rw [Nat.digits_def' (by norm_num) (by omega), Nat.ofDigits_cons]
    rw [show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]
    simp

theorem v_odd (m : ℕ) : v (2 * m + 1) = 1 + 3 * v m := by
  unfold v
  rw [Nat.digits_def' (by norm_num) (by omega), Nat.ofDigits_cons]
  rw [show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]

theorem gen_of (m : ℕ) : Gen (6 * v m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa [v] using Gen.one
    · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
      · have hk : k < 2 * k := by omega
        have := Gen.f _ (ih k hk)
        rw [v_even]
        convert this using 1
        omega
      · have hk : k < 2 * k + 1 := by omega
        have := Gen.g _ (ih k hk)
        rw [v_odd]
        convert this using 1
        ring

theorem of_gen (x : ℕ) (h : Gen x) : ∃ m, x = 6 * v m + 1 := by
  induction h with
  | one => exact ⟨0, by simp [v]⟩
  | f x _ ih =>
    obtain ⟨m, rfl⟩ := ih
    exact ⟨2 * m, by rw [v_even]; omega⟩
  | g x _ ih =>
    obtain ⟨m, rfl⟩ := ih
    exact ⟨2 * m + 1, by rw [v_odd]; ring⟩

end OMA.P_oeis_a055246

open OMA.P_oeis_a055246 in
theorem OMA.solution : type_of% @OMA.S_oeis_a055246.main := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, _, rfl⟩
    exact gen_of (n - 1)
  · intro h
    obtain ⟨m, rfl⟩ := of_gen x h
    exact ⟨m + 1, by omega, by simp [a, v]⟩
