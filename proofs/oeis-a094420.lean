import OMAStatements.S_oeis_a094420
import Mathlib

namespace A094420P

open Finset

theorem pow_expand (n : ℕ) : ∀ j : ℕ,
    j ^ n = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k * k.factorial * j.choose k := by
  induction n with
  | zero => intro j; simp
  | succ n ih =>
    intro j
    have key : ∀ k : ℕ, j * j.choose k = k * j.choose k + (k + 1) * j.choose (k + 1) := by
      intro k
      have h := Nat.choose_succ_right_eq j k
      rcases le_or_gt k j with hk | hk
      · have : j = k + (j - k) := by omega
        calc j * j.choose k = (k + (j - k)) * j.choose k := by rw [← this]
          _ = k * j.choose k + (k + 1) * j.choose (k + 1) := by rw [add_mul]; linarith
      · rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]; simp
    have e1 : j ^ (n + 1) = ∑ k ∈ range (n + 1),
        (Nat.stirlingSecond n k * k.factorial * (k * j.choose k)
          + Nat.stirlingSecond n k * k.factorial * ((k + 1) * j.choose (k + 1))) := by
      rw [pow_succ, ih j, sum_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_assoc, mul_comm (j.choose k) j, key k]; ring
    have e2 : ∑ k ∈ range (n + 1 + 1),
        Nat.stirlingSecond (n + 1) k * k.factorial * j.choose k = ∑ k ∈ range (n + 1),
        ((k + 1) * Nat.stirlingSecond n (k + 1) * (k + 1).factorial * j.choose (k + 1)
          + Nat.stirlingSecond n k * k.factorial * ((k + 1) * j.choose (k + 1))) := by
      rw [sum_range_succ']
      simp only [Nat.stirlingSecond_succ_zero, zero_mul, add_zero, Nat.stirlingSecond_succ_succ]
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.factorial_succ]; ring
    have e3 : ∑ k ∈ range (n + 1), Nat.stirlingSecond n k * k.factorial * (k * j.choose k)
        = ∑ k ∈ range (n + 1),
          (k + 1) * Nat.stirlingSecond n (k + 1) * (k + 1).factorial * j.choose (k + 1) := by
      rw [sum_range_succ', sum_range_succ,
        Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp only [zero_mul, mul_zero, add_zero]
      refine sum_congr rfl fun k _ => ?_
      ring
    rw [e1, e2, sum_add_distrib, sum_add_distrib, e3]

theorem hasSum_choose (k : ℕ) {z : ℝ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => (j.choose k : ℝ) * z ^ j) (z ^ k / (1 - z) ^ (k + 1)) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k hz).mul_left (z ^ k)
  have h0 : ∑ i ∈ range k, (i.choose k : ℝ) * z ^ i = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]; simp
  have h' : HasSum (fun m : ℕ => (((m + k).choose k : ℕ) : ℝ) * z ^ (m + k))
      (z ^ k / (1 - z) ^ (k + 1)) := by
    have e : (fun m : ℕ => (((m + k).choose k : ℕ) : ℝ) * z ^ (m + k))
        = fun i : ℕ => z ^ k * ((((i + k).choose k : ℕ) : ℝ) * z ^ i) := by
      funext m; rw [pow_add]; ring
    rw [e, div_eq_mul_one_div]; exact h
  exact (hasSum_nat_add_iff' (f := fun j : ℕ => (j.choose k : ℝ) * z ^ j) k).mp
    (by rw [h0, sub_zero]; exact h')

theorem main_aux (n : ℕ) (hn : 0 < n) (a : ℕ)
    (ha : a = ∑ k ∈ range (n + 1), k.factorial * n ^ k * Nat.stirlingSecond n k) :
    HasSum (fun j : ℕ => (j : ℝ) ^ n * ((n : ℝ) / ((n : ℝ) + 1)) ^ j)
      (((n : ℝ) + 1) * (a : ℝ)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set z : ℝ := (n : ℝ) / ((n : ℝ) + 1) with hzdef
  have hz : ‖z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hzdef, div_lt_one hn1]; linarith
  have h1z : 1 - z = 1 / ((n : ℝ) + 1) := by rw [hzdef]; field_simp; ring
  have hs := hasSum_sum (f := fun (k : ℕ) (j : ℕ) =>
      ((Nat.stirlingSecond n k : ℝ) * (k.factorial : ℝ)) * ((j.choose k : ℝ) * z ^ j))
    (s := range (n + 1)) (fun k _ => (hasSum_choose k hz).mul_left _)
  convert hs using 1
  · funext j
    have := congrArg (Nat.cast : ℕ → ℝ) (pow_expand n j)
    push_cast at this
    rw [this, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    ring
  · rw [ha]; push_cast; rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [h1z, hzdef, div_pow, one_div, inv_pow, pow_succ]
    field_simp

end A094420P

theorem OMA.solution : type_of% @OMA.S_oeis_a094420.main :=
  fun n hn => A094420P.main_aux n hn (OMA.S_oeis_a094420.a n) rfl
