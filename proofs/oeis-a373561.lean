import OMAStatements.S_oeis_a373561
import Mathlib

namespace OMA.P_oeis_a373561

open Finset OMA.S_oeis_a373561

theorem sum_sq (n : ℕ) :
    (∑ x ∈ range n, ((x : ℤ) + 1) ^ 2) = (n : ℤ) * (n + 1) * (2 * n + 1) / 6 := by
  have h : ∀ m : ℕ, 6 * (∑ x ∈ range m, ((x : ℤ) + 1) ^ 2) = (m : ℤ) * (m + 1) * (2 * m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, mul_add, ih]
      push_cast
      ring
  rw [← h n]
  omega

theorem grouped_eq (n : ℕ) (hn : n ≠ 0) :
    groupedSum n = ∑ z ∈ range n, ∑ y ∈ range n, ∑ x ∈ range n,
      weight (x+1) (y+1) (z+1) := by
  unfold groupedSum
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_ite_eq]
  have h1 : 0 < Int.gcd (weight (x+1) (y+1) (z+1)) n :=
    Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn)
  have h2 : Int.gcd (weight (x+1) (y+1) (z+1)) n ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (by
      have := Int.gcd_dvd_right (weight (x+1) (y+1) (z+1)) (n : ℤ)
      exact_mod_cast this)
  rw [if_pos (by simp only [mem_Icc]; omega)]

end OMA.P_oeis_a373561

open OMA.P_oeis_a373561 OMA.S_oeis_a373561 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a373561.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [groupedSum]
  rw [grouped_eq n hn.ne']
  have hS := sum_sq n
  have h6 : (6 : ℤ) ∣ (n : ℤ) * (n + 1) * (2 * n + 1) := by
    have h : ∀ m : ℕ, 6 * (∑ x ∈ range m, ((x : ℤ) + 1) ^ 2) = (m : ℤ) * (m + 1) * (2 * m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_range_succ, mul_add, ih]
        push_cast
        ring
    exact ⟨_, (h n).symm⟩
  have key : (∑ z ∈ range n, ∑ y ∈ range n, ∑ x ∈ range n, weight (x+1) (y+1) (z+1))
      = (n : ℤ) ^ 2 * ∑ x ∈ range n, ((x : ℤ) + 1) ^ 2 := by
    have e1 : ∀ y z : ℕ, (∑ x ∈ range n, weight (x+1) (y+1) (z+1)) =
        (∑ x ∈ range n, ((x : ℤ) + 1) ^ 2) + n * ((y : ℤ) + 1) ^ 2 - n * ((z : ℤ) + 1) ^ 2 := by
      intro y z
      simp only [weight, sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring
    simp only [e1, sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
      ← mul_sum]
    ring
  rw [key, hS]
  obtain ⟨c, hc⟩ := h6
  rw [hc, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hq : ((c : ℤ) : ℚ) = ((n : ℚ) * (n + 1) * (2 * n + 1)) / 6 := by
    have : ((6 * c : ℤ) : ℚ) = (((n : ℤ) * (n + 1) * (2 * n + 1) : ℤ) : ℚ) := by rw [hc]
    push_cast at this
    linarith
  push_cast
  rw [hq]
  ring
