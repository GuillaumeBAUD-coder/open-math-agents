import OMAStatements.S_oeis_a266753

open OMA.S_oeis_a266753 Finset PowerSeries

private theorem rule_163 (l c r : Bool) :
    ruleOut 163 l c r = if l then r else !c := by
  cases l <;> cases c <;> cases r <;> decide

private def pattern (n : ℕ) (j : ℤ) : Bool :=
  decide (j ≤ 0 ∨ 2*(n:ℤ) < j ∨ (3 ≤ j ∧ j % 2 = 1))

private theorem pattern_step (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    (if pattern n (j-2) then pattern n j else !(pattern n (j-1))) = pattern (n+1) j := by
  simp only [pattern, decide_eq_true_eq]
  split_ifs <;> simp only [← decide_not, decide_eq_decide] <;> push_cast <;> omega

private theorem cell_pattern (n : ℕ) (hn : 1 ≤ n) (i : ℤ) :
    cell 163 n i = pattern n (i+n) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      simp only [cell, rule_163, pattern, decide_eq_true_eq]
      split_ifs <;> simp only [← decide_not, decide_eq_decide] <;> push_cast <;> omega
    · simp only [cell, rule_163, ih (by omega) (i-1), ih (by omega) i, ih (by omega) (i+1)]
      have h₁ : i-1+(n:ℤ) = (i+(n+1:ℕ))-2 := by push_cast; ring
      have h₂ : i+(n:ℤ) = (i+(n+1:ℕ))-1 := by push_cast; ring
      have h₃ : i+1+(n:ℤ) = i+(n+1:ℕ) := by push_cast; ring
      rw [h₁,h₂,h₃]
      exact pattern_step n (by omega) _

private theorem a_zero : a 0 = 1 := by decide +kernel

private theorem a_one : a 1 = 4 := by decide +kernel

private theorem a_two : a 2 = 18 := by decide +kernel

private theorem digits_sum (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ j ∈ range (2*n+1), (if pattern n (j:ℤ) then (2:ℤ)^(2*n-j) else 0) := by
  unfold a
  apply sum_congr rfl
  intro j _
  rw [cell_pattern n hn, sub_add_cancel]

private theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n+1) = 4*a n+2 := by
  rw [digits_sum (n+1) (by omega), digits_sum n hn]
  have hlen : 2*(n+1)+1 = (2*n+1)+1+1 := by omega
  rw [hlen, sum_range_succ, sum_range_succ, mul_sum]
  have h₁ : pattern (n+1) ↑(2*n+1) = true := by
    simp only [pattern, decide_eq_true_eq]
    push_cast
    omega
  have h₂ : pattern (n+1) ↑(2*n+1+1) = false := by
    simp only [pattern, decide_eq_false_iff_not]
    push_cast
    omega
  rw [h₁, h₂, if_pos rfl]
  simp only [if_false, Bool.false_eq_true, add_zero]
  have hpow : 2*(n+1) - (2*n+1) = 1 := by omega
  rw [hpow, pow_one]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ 2*n := by simpa using Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hpat : pattern (n+1) (j:ℤ) = pattern n (j:ℤ) := by
    simp only [pattern, decide_eq_decide]
    push_cast
    omega
  have hex : 2*(n+1)-j = (2*n-j)+2 := by omega
  rw [hpat, hex, pow_add]
  split_ifs <;> ring

private theorem two_step (n : ℕ) (hn : 2 < n) :
    a n = 5*a (n-1)-4*a (n-2) := by
  have h₁ := a_step (n-1) (by omega)
  have h₂ := a_step (n-2) (by omega)
  rw [show n-1+1=n by omega] at h₁
  rw [show n-2+1=n-1 by omega] at h₂
  linarith

private theorem a_closed (n : ℕ) : (a (n+1):ℚ) = (14/3)*4^n - 2/3 := by
  induction n with
  | zero => norm_num [a_one]
  | succ n ih =>
    rw [a_step (n+1) (by omega)]
    push_cast
    rw [ih, pow_succ]
    ring

private theorem series_identity :
    (PowerSeries.mk (fun n => (a n : ℚ))) * ((1-X)*(1-4*X)) = 1-X+2*X^2 := by
  have hd : ((1-X)*(1-4*X) : ℚ⟦X⟧) = 1-C 5 * X+C 4 * X^2 := by
    simp only [map_ofNat]
    ring
  have hright : (1-X+2*X^2 : ℚ⟦X⟧) = 1-X+C 2*X^2 := by simp only [map_ofNat]
  rw [hd,hright,mul_add,mul_sub,mul_one,←mul_assoc,←mul_assoc]
  ext n
  have hx : (X : ℚ⟦X⟧) = X^1 := (pow_one _).symm
  conv_lhs => arg 2; arg 1; arg 2; rw [hx]
  simp only [map_add,map_sub,coeff_mul_X_pow',coeff_mul_C,coeff_mk,coeff_one,
    coeff_X,coeff_C]
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num [a_zero,a_one,a_two]
  · norm_num [show n ≠ 0 by omega, show n ≠ 1 by omega, show n-2 ≠ 0 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega]
    have h := congrArg (fun z : ℤ => (z:ℚ)) (two_step n (by omega))
    push_cast at h
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a266753.main := by
  refine ⟨two_step,series_identity,?_,?_⟩
  · intro n hn
    have h := a_step (n-1) (by omega)
    rwa [show n-1+1=n by omega] at h
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [a_closed, show k+1-1=k by omega, show 2*(k+1)-1=2*k+1 by omega]
    unfold A020988
    rw [pow_succ (4:ℚ), pow_succ (2:ℚ), pow_mul]
    norm_num
    constructor <;> ring