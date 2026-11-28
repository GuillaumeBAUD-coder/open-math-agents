import OMAStatements.S_oeis_a040027

namespace OMA.GouldAlternatingFactorials

open Finset OMA.S_oeis_a040027

private def S (n k : ℕ) : ℤ := Nat.stirlingSecond n k

private theorem stirling_step (n k : ℕ) :
    S (n + 1) (k + 1) = (k + 1 : ℤ) * S n (k + 1) + S n k := by
  simp [S, Nat.stirlingSecond_succ_succ]

/-- Partition according to the block containing the last element. -/
private theorem binomial_stirling (n k : ℕ) :
    (∑ i ∈ range (n + 1), (n.choose i : ℤ) * S i k) = S (n + 1) (k + 1) := by
  induction n generalizing k with
  | zero =>
    rw [stirling_step]
    simp [S]
  | succ n ih =>
    cases k with
    | zero =>
      rw [sum_range_succ']
      simp [S, Nat.stirlingSecond_succ_zero, Nat.stirlingSecond_one_right]
    | succ k =>
      rw [sum_choose_succ_mul (fun i _ => S i (k + 1)) n]
      simp_rw [fun i => stirling_step i k, mul_add, sum_add_distrib,
        mul_left_comm (↑(n.choose _) : ℤ)]
      rw [← mul_sum, ih, ih, stirling_step (n + 1) (k + 1)]
      push_cast
      ring

private def w (k : ℕ) : ℤ := (-1 : ℤ) ^ k * k.factorial

private theorem w_step (k : ℕ) : w (k + 1) = - w k * (k + 1 : ℤ) := by
  unfold w
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  ring

/-- The signed factorial weights cancel by the two terms in Stirling's recurrence. -/
private theorem weighted_cancellation (n : ℕ) :
    (∑ k ∈ range (n + 2), w k * S (n + 2) (k + 1)) = 0 := by
  simp_rw [stirling_step (n + 1), mul_add, sum_add_distrib]
  rw [sum_range_succ (fun k => w k * ((k + 1 : ℤ) * S (n + 1) (k + 1))),
    sum_range_succ' (fun k => w k * S (n + 1) k)]
  have hz : S (n + 1) (n + 2) = 0 := by
    simp [S, Nat.stirlingSecond_eq_zero_of_lt]
  have hzero : S (n + 1) 0 = 0 := by simp [S]
  rw [hz, hzero, mul_zero, mul_zero, mul_zero, add_zero, add_zero]
  simp_rw [w_step, neg_mul, ← mul_assoc, sum_neg_distrib]
  exact add_neg_cancel _

private def B (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), altFact k * S (n + 1) (k + 1)

private theorem B_extend {i n : ℕ} (h : i < n) :
    B i = ∑ k ∈ range n, altFact k * S (i + 1) (k + 1) := by
  unfold B
  refine sum_subset (range_mono (by omega)) fun k hk hki => ?_
  have hz : i + 1 < k + 1 := by
    rw [mem_range] at hki
    omega
  simp [S, Nat.stirlingSecond_eq_zero_of_lt hz]

private theorem recurrence_B (n : ℕ) :
    B (n + 1) = ∑ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℤ) * B i := by
  have hswap :
      (∑ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℤ) * B i) =
      ∑ k ∈ range (n + 1), altFact k * S (n + 2) (k + 2) := by
    calc
      _ = ∑ i ∈ range (n + 1), ∑ k ∈ range (n + 1),
          altFact k * (((n + 1).choose (i + 1) : ℤ) * S (i + 1) (k + 1)) := by
        refine sum_congr rfl fun i hi => ?_
        rw [B_extend (mem_range.mp hi), mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_sum]
        congr 1
        have hc := binomial_stirling (n + 1) (k + 1)
        rw [sum_range_succ', show S 0 (k + 1) = 0 by simp [S],
          mul_zero, add_zero] at hc
        exact hc
  rw [hswap]
  have hb : ∀ k : ℕ, altFact (k + 1) = altFact k + w (k + 1) := by
    intro k
    exact sum_range_succ _ _
  have h0 : altFact 0 = w 0 := by simp [altFact, w]
  have vanish := weighted_cancellation n
  rw [sum_range_succ'] at vanish
  unfold B
  rw [sum_range_succ', h0]
  simp_rw [hb, add_mul, sum_add_distrib]
  linarith

private theorem recurrence_a (n : ℕ) :
    a (n + 1) = ∑ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℤ) * a i := by
  cases n with
  | zero => simp [a.eq_1, a.eq_2]
  | succ n =>
    rw [a.eq_3]
    let f (i : ℕ) : ℤ := if i = 0 then 0 else ((n + 2).choose (i + 1) : ℤ) * a i
    change (n + 2 : ℤ) + (∑ j : Fin (n + 2), f j) =
      ∑ i ∈ range (n + 2), ((n + 2).choose (i + 1) : ℤ) * a i
    rw [Fin.sum_univ_eq_sum_range f, sum_range_succ' f (n + 1),
      sum_range_succ' (fun i => ((n + 2).choose (i + 1) : ℤ) * a i) (n + 1)]
    simp [f, a.eq_1, add_comm]

theorem identity (n : ℕ) : a n = B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [B, altFact, S, a.eq_1, show Nat.stirlingSecond 1 1 = 1 from Nat.stirlingSecond_one_right 0]
    | succ n =>
      rw [recurrence_a, recurrence_B]
      exact sum_congr rfl fun i hi => by rw [ih i (mem_range.mp hi)]

end OMA.GouldAlternatingFactorials

theorem OMA.solution : type_of% @OMA.S_oeis_a040027.main :=
  OMA.GouldAlternatingFactorials.identity
