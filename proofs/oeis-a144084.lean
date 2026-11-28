import OMAStatements.S_oeis_a144084
import Mathlib

namespace OMA.P144084

open Finset

/-- F(n, q) = Sum_i c(n, i) * S(i+1, q). -/
def F (n q : ℕ) : ℕ := ∑ i ∈ range (n + 1), Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1) q

lemma n_mul_c0 (n : ℕ) : n * Nat.stirlingFirst n 0 = 0 := by
  rcases n with _ | n
  · simp
  · rw [Nat.stirlingFirst_succ_zero, mul_zero]

lemma F_zero (n : ℕ) : F n 0 = 0 := by
  unfold F
  apply Finset.sum_eq_zero
  intro i _
  rw [Nat.stirlingSecond_succ_zero, mul_zero]

lemma F_succ (n q : ℕ) : F (n + 1) (q + 1) = (n + q + 1) * F n (q + 1) + F n q := by
  unfold F
  rw [Finset.sum_range_succ' (fun i => Nat.stirlingFirst (n + 1) i * Nat.stirlingSecond (i + 1) (q + 1)) (n + 1)]
  rw [Nat.stirlingFirst_succ_zero, zero_mul, add_zero]
  have h1 : ∀ i, Nat.stirlingFirst (n + 1) (i + 1) * Nat.stirlingSecond (i + 1 + 1) (q + 1)
      = n * (Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (q + 1))
        + (q + 1) * (Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1) (q + 1))
        + Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1) q := by
    intro i
    rw [Nat.stirlingFirst_succ_succ, Nat.stirlingSecond_succ_succ (i + 1) q]
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hU : n * ∑ i ∈ range (n + 1), Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (q + 1)
      = n * ∑ i ∈ range (n + 1), Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1) (q + 1) := by
    rw [Finset.sum_range_succ (fun i => Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (q + 1)) n,
      Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), zero_mul, add_zero]
    rw [Finset.sum_range_succ' (fun i => Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1) (q + 1)) n]
    rw [mul_add, ← mul_assoc, n_mul_c0, zero_mul, add_zero]
  rw [hU]
  ring

/-- m! * F(n, m+1) = n! * C(n, m). -/
lemma G (n : ℕ) : ∀ m : ℕ, m.factorial * F n (m + 1) = n.factorial * n.choose m := by
  induction n with
  | zero =>
    intro m
    unfold F
    rcases m with _ | m
    · simp [Nat.stirlingSecond_self]
    · simp [Nat.stirlingSecond_eq_zero_of_lt]
  | succ n ih =>
    intro m
    rw [F_succ]
    rcases m with _ | m
    · have h1 := ih 0
      simp only [Nat.factorial_zero, one_mul, Nat.choose_zero_right, mul_one, zero_add] at h1 ⊢
      rw [F_zero, add_zero, h1, Nat.factorial_succ]
    · have i1 := ih (m + 1)
      have i0 := ih m
      have hc := Nat.choose_succ_right_eq n m
      rw [Nat.factorial_succ n, Nat.choose_succ_succ]
      have e : (m + 1).factorial * ((n + (m + 1) + 1) * F n (m + 1 + 1) + F n (m + 1))
          = (n + m + 2) * ((m + 1).factorial * F n (m + 1 + 1)) + (m + 1) * (m.factorial * F n (m + 1)) := by
        rw [Nat.factorial_succ m]
        ring
      rw [e, i1, i0]
      rcases Nat.lt_or_ge n m with hlt | hge
      · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega : n < m + 1)]
        simp
      · obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
        rw [Nat.add_sub_cancel_left] at hc
        have e2 : (m + d + m + 2) * ((m + d).factorial * (m + d).choose (m + 1))
            + (m + 1) * ((m + d).factorial * (m + d).choose m)
            = (m + d).factorial * ((m + d).choose (m + 1) * (m + 1))
              + (m + d + 1) * (m + d).factorial * (m + d).choose (m + 1)
              + (m + 1) * ((m + d).factorial * (m + d).choose m) := by ring
        rw [e2, hc]
        ring

end OMA.P144084

theorem OMA.solution : type_of% @OMA.S_oeis_a144084.main := by
  intro n k hk
  unfold OMA.S_oeis_a144084.T
  have hsum : ∑ j ∈ Finset.range (k + 1),
      Nat.stirlingFirst n (n - j) * Nat.stirlingSecond (n - j + 1) (n - k + 1)
      = OMA.P144084.F n (n - k + 1) := by
    unfold OMA.P144084.F
    rw [← Finset.sum_range_reflect
      (fun i => Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1) (n - k + 1)) (n + 1)]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hx'
      simp only [Finset.mem_range] at hx hx'
      rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), mul_zero]
  rw [hsum]
  have hG := OMA.P144084.G n (n - k)
  rw [Nat.choose_symm hk] at hG
  have hf := Nat.choose_mul_factorial_mul_factorial hk
  have hpos : 0 < (n - k).factorial := Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hG, ← hf]
  ring
