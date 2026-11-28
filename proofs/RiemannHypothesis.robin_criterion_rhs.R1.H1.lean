import OMAReductions.R_RiemannHypothesis_robin_criterion_rhs_R1

/-!
Verify the integer comparison in Robin's reduction for each n from 1 to
5040. Divisor sums are computed from their prime factorizations.
-/

open scoped ArithmeticFunction.sigma
open Finset

private def sigmaFast (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    (n.primeFactorsList.dedup.map fun p =>
      ∑ j ∈ range (n.primeFactorsList.count p + 1), p ^ j).prod

private theorem sigmaFast_eq (n : ℕ) : sigmaFast n = σ 1 n := by
  by_cases h : n = 0
  · simp [sigmaFast, h]
  · have same : n.primeFactorsList.dedup.toFinset = n.primeFactors := by
      change n.primeFactorsList.dedup.toFinset = n.primeFactorsList.toFinset
      ext p
      simp only [List.mem_toFinset, List.mem_dedup]
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors h, ← same]
    rw [List.prod_toFinset _ (List.nodup_dedup _)]
    simp only [sigmaFast, if_neg h, Nat.primeFactorsList_count_eq]

private def bounds (start length : ℕ) : Bool :=
  (List.range' start length).all fun n =>
    decide ((sigmaFast n * 55440)^28 * 55440 < (232128 * n)^28 * n)

set_option maxRecDepth 20000 in
private theorem refSigma : σ 1 55440 = 232128 := by
  rw [← sigmaFast_eq]
  decide +kernel

private theorem joinRange {start left right : ℕ}
    (hLeft : bounds start left = true) (hRight : bounds (start + left) right = true) :
    bounds start (left + right) = true := by
  unfold bounds at *
  rw [← List.range'_append_1, List.all_append, Bool.and_eq_true]
  exact ⟨hLeft, hRight⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1 : bounds 1 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked113 : bounds 113 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked225 : bounds 225 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked337 : bounds 337 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked449 : bounds 449 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked561 : bounds 561 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked673 : bounds 673 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked785 : bounds 785 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked897 : bounds 897 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1009 : bounds 1009 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1121 : bounds 1121 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1233 : bounds 1233 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1345 : bounds 1345 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1457 : bounds 1457 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1569 : bounds 1569 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1681 : bounds 1681 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1793 : bounds 1793 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked1905 : bounds 1905 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2017 : bounds 2017 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2129 : bounds 2129 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2241 : bounds 2241 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2353 : bounds 2353 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2465 : bounds 2465 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2577 : bounds 2577 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2689 : bounds 2689 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2801 : bounds 2801 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked2913 : bounds 2913 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3025 : bounds 3025 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3137 : bounds 3137 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3249 : bounds 3249 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3361 : bounds 3361 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3473 : bounds 3473 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3585 : bounds 3585 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3697 : bounds 3697 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3809 : bounds 3809 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked3921 : bounds 3921 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4033 : bounds 4033 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4145 : bounds 4145 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4257 : bounds 4257 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4369 : bounds 4369 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4481 : bounds 4481 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4593 : bounds 4593 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4705 : bounds 4705 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4817 : bounds 4817 112 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checked4929 : bounds 4929 112 = true := by
  decide +kernel

private theorem checked : bounds 1 5040 = true := by
  apply joinRange (right := 4928) checked1
  apply joinRange (right := 4816) checked113
  apply joinRange (right := 4704) checked225
  apply joinRange (right := 4592) checked337
  apply joinRange (right := 4480) checked449
  apply joinRange (right := 4368) checked561
  apply joinRange (right := 4256) checked673
  apply joinRange (right := 4144) checked785
  apply joinRange (right := 4032) checked897
  apply joinRange (right := 3920) checked1009
  apply joinRange (right := 3808) checked1121
  apply joinRange (right := 3696) checked1233
  apply joinRange (right := 3584) checked1345
  apply joinRange (right := 3472) checked1457
  apply joinRange (right := 3360) checked1569
  apply joinRange (right := 3248) checked1681
  apply joinRange (right := 3136) checked1793
  apply joinRange (right := 3024) checked1905
  apply joinRange (right := 2912) checked2017
  apply joinRange (right := 2800) checked2129
  apply joinRange (right := 2688) checked2241
  apply joinRange (right := 2576) checked2353
  apply joinRange (right := 2464) checked2465
  apply joinRange (right := 2352) checked2577
  apply joinRange (right := 2240) checked2689
  apply joinRange (right := 2128) checked2801
  apply joinRange (right := 2016) checked2913
  apply joinRange (right := 1904) checked3025
  apply joinRange (right := 1792) checked3137
  apply joinRange (right := 1680) checked3249
  apply joinRange (right := 1568) checked3361
  apply joinRange (right := 1456) checked3473
  apply joinRange (right := 1344) checked3585
  apply joinRange (right := 1232) checked3697
  apply joinRange (right := 1120) checked3809
  apply joinRange (right := 1008) checked3921
  apply joinRange (right := 896) checked4033
  apply joinRange (right := 784) checked4145
  apply joinRange (right := 672) checked4257
  apply joinRange (right := 560) checked4369
  apply joinRange (right := 448) checked4481
  apply joinRange (right := 336) checked4593
  apply joinRange (right := 224) checked4705
  apply joinRange (right := 112) checked4817
  exact checked4929

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.H1 := by
  intro n positive upper
  have hmem : n ∈ List.range' 1 5040 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
  have comparison := of_decide_eq_true (List.all_eq_true.mp checked n hmem)
  simpa only [sigmaFast_eq, refSigma] using comparison
