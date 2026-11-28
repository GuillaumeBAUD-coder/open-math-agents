import OMAStatements.S_oeis_a325689
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: write a n as a double sum over (x,y) with z = n-x-y, count each inner sum as
-- (n-1-x) minus the excluded y values, then sum using a triangular-number lemma, split by parity.

namespace OMA.A325689Proof
open OMA.S_oeis_a325689
open Finset in
lemma a_eq (n : ℕ) : (a n : ℤ) = ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n,
    (if (x + y < n ∧ 2 * x ≠ n ∧ 2 * y ≠ n ∧ 2 * (x + y) ≠ n) then (1 : ℤ) else 0) := by
  unfold a
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun y hy => ?_
  simp only [Finset.mem_Icc] at hx hy
  by_cases hxy : x + y < n
  swap
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro z hz
    simp only [Finset.mem_Icc] at hz
    dsimp only
    rw [if_neg]
    omega
  rw [Finset.sum_eq_single (n - x - y)]
  · dsimp only
    split_ifs <;> omega
  · intro z _ hz
    dsimp only
    rw [if_neg]
    omega
  · intro h
    simp only [Finset.mem_Icc, not_and_or, not_le] at h
    dsimp only
    rw [if_neg]
    omega

open Finset in
lemma inner_sum (n x : ℕ) (hx1 : 1 ≤ x) : ∑ y ∈ Icc 1 n,
    (if (x + y < n ∧ 2 * x ≠ n ∧ 2 * y ≠ n ∧ 2 * (x + y) ≠ n) then (1 : ℤ) else 0) =
    if 2 * x = n then 0 else ((n - 1 - x : ℕ) : ℤ) - (if n % 2 = 0 ∧ 2 * x < n then 2 else 0) := by
  by_cases hx2 : 2 * x = n
  · rw [if_pos hx2]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    omega
  · rw [if_neg hx2, Finset.sum_boole]
    have h1 := Finset.card_filter_add_card_filter_not (s := Ico 1 (n - x))
      (p := fun y => 2 * y ≠ n ∧ 2 * (x + y) ≠ n)
    have h2 : (Icc 1 n).filter (fun y => x + y < n ∧ 2 * x ≠ n ∧ 2 * y ≠ n ∧ 2 * (x + y) ≠ n)
        = (Ico 1 (n - x)).filter (fun y => 2 * y ≠ n ∧ 2 * (x + y) ≠ n) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      omega
    have h3 : ((Ico 1 (n - x)).filter (fun y => ¬ (2 * y ≠ n ∧ 2 * (x + y) ≠ n))).card
        = if n % 2 = 0 ∧ 2 * x < n then 2 else 0 := by
      split_ifs with h
      · rw [Finset.card_eq_two]
        refine ⟨n / 2, n / 2 - x, by omega, ?_⟩
        ext y
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
        omega
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y hy
        simp only [Finset.mem_Ico] at hy
        omega
    rw [h2]
    rw [Nat.card_Ico] at h1
    split_ifs at h3 ⊢ <;> omega

open Finset in
lemma tri (N : ℕ) : 2 * ∑ x ∈ Icc 1 N, (N - x) + N = N * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : ∑ x ∈ Icc 1 N, (N + 1 - x) = ∑ x ∈ Icc 1 N, (N - x) + N := by
      rw [Finset.sum_congr rfl (g := fun x => (N - x) + 1)]
      · rw [Finset.sum_add_distrib]
        simp
      · intro x hx
        simp only [Finset.mem_Icc] at hx
        omega
    rw [this]
    simp only [Nat.sub_self, add_zero]
    nlinarith [ih]

open Finset in
lemma tri' (N : ℕ) : 2 * ((∑ x ∈ Icc 1 (N + 1), ((N - x : ℕ) : ℤ))) + N = N * N := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  have := tri N
  have h := congrArg (Nat.cast : ℕ → ℤ) this
  push_cast at h
  simp only [Nat.sub_eq_zero_of_le (Nat.le_succ N), Nat.cast_zero, add_zero]
  exact h
end OMA.A325689Proof

open OMA.S_oeis_a325689 in
theorem OMA.solution : type_of% @OMA.S_oeis_a325689.main := by
  intro n hn
  rw [OMA.A325689Proof.a_eq, Finset.sum_congr rfl (fun x hx => OMA.A325689Proof.inner_sum n x (Finset.mem_Icc.1 hx).1)]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hs : ∀ x ∈ Finset.Icc 1 (2 * (k + 1)),
        (if 2 * x = 2 * (k + 1) then (0 : ℤ) else ((2 * (k + 1) - 1 - x : ℕ) : ℤ) -
          (if 2 * (k + 1) % 2 = 0 ∧ 2 * x < 2 * (k + 1) then 2 else 0)) =
        ((2 * k + 1 - x : ℕ) : ℤ) - (if x = k + 1 then (k : ℤ) else 0) -
          2 * (if x < k + 1 then 1 else 0) := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hs, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_ite_eq', if_pos (by simp only [Finset.mem_Icc]; omega), Finset.sum_boole]
    have hc : ((Finset.Icc 1 (2 * (k + 1))).filter (fun x => x < k + 1)).card = k := by
      rw [show (Finset.Icc 1 (2 * (k + 1))).filter (fun x => x < k + 1) = Finset.Ico 1 (k + 1) by
        ext x; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega]
      simp
    rw [hc]
    have ht := OMA.A325689Proof.tri' (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at ht
    have hp : (-1 : ℤ) ^ (2 * (k + 1)) = 1 := by rw [pow_mul]; norm_num
    have he : -(5 + 3 * (-1 : ℤ) ^ (2 * (k + 1)) - 2 * ((2 * (k + 1) : ℕ) : ℤ)) *
        (((2 * (k + 1) : ℕ) : ℤ) - 2) = 4 * (2 * k * (k - 1)) := by
      rw [hp]; push_cast; ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num)]
    push_cast at ht ⊢
    linarith
  · have hs : ∀ x ∈ Finset.Icc 1 (2 * m + 1),
        (if 2 * x = 2 * m + 1 then (0 : ℤ) else ((2 * m + 1 - 1 - x : ℕ) : ℤ) -
          (if (2 * m + 1) % 2 = 0 ∧ 2 * x < 2 * m + 1 then 2 else 0)) =
        ((2 * m - x : ℕ) : ℤ) := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hs]
    have ht := OMA.A325689Proof.tri' (2 * m)
    have hp : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have he : -(5 + 3 * (-1 : ℤ) ^ (2 * m + 1) - 2 * ((2 * m + 1 : ℕ) : ℤ)) *
        (((2 * m + 1 : ℕ) : ℤ) - 2) = 4 * (m * (2 * m - 1)) := by
      rw [hp]; push_cast; ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num)]
    push_cast at ht ⊢
    linarith
