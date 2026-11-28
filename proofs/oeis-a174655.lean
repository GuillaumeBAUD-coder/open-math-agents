import OMAStatements.S_oeis_a174655

open OMA.S_oeis_a174655
private theorem tail_formula (n : ℕ) :
    2*tail n = 9 - (-1 : ℤ)^n - 8*((n:ℤ)+3) + 4*((n:ℤ)+3)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | n+4 =>
      have h0 := ih n (by omega)
      have h1 := ih (n+1) (by omega)
      have h3 := ih (n+3) (by omega)
      rw [tail]
      push_cast at *
      rw [pow_add] at h1 h3 ⊢
      norm_num at h1 h3 ⊢
      linarith only [h0,h1,h3]
private theorem closed (n : ℕ) (hn : 1 < n) :
    12*a n = 3*(-9+(-1 : ℤ)^n)+34*(n:ℤ)-12*(n:ℤ)^2+8*(n:ℤ)^3 := by
  obtain ⟨j,rfl⟩ : ∃ j : ℕ, n = j+2 := ⟨n-2,by omega⟩
  induction j with
  | zero => decide
  | succ j ih =>
    have ih' := ih (by omega)
    rw [show j+1+2 = (j+2)+1 by omega,a,Finset.sum_range_succ]
    change 12*(a (j+2) + b (j+2+1)) = _
    rw [show j+2+1 = j+3 by omega,b]
    have ht := tail_formula j
    push_cast at *
    rw [show j+2+1 = j+3 by omega, pow_add] 
    rw [pow_add] at ih'
    norm_num at ih' ⊢
    linarith only [ht,ih']


set_option maxHeartbeats 1000000 in
open PowerSeries in
private theorem gf :
    ((X-1)^4*(X+1) * mk a : ℤ⟦X⟧) = X*(X^5-X^4+3*X^3+2*X^2+2*X+1) := by
  have hden : ((X-1)^4*(X+1) : ℤ⟦X⟧) =
      X^5 - C (3:ℤ)*X^4 + C (2:ℤ)*X^3 + C (2:ℤ)*X^2 - C (3:ℤ)*X^1 + X^0 := by
    norm_num
    ring
  have hnum : (X*(X^5-X^4+3*X^3+2*X^2+2*X+1) : ℤ⟦X⟧) =
      X^6 - X^5 + C (3:ℤ)*X^4 + C (2:ℤ)*X^3 + C (2:ℤ)*X^2 + X^1 := by
    norm_num
    ring
  rw [hden,hnum]
  ext n
  simp only [add_mul,sub_mul,map_add,map_sub,mul_assoc,coeff_C_mul,coeff_X_pow_mul',coeff_mk,coeff_X_pow]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [a,b,tail,Finset.sum_range_succ]
  · obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+7 := ⟨n-7,by omega⟩
    clear hn
    have e1 : k+7-1 = k+6 := by omega
    have e2 : k+7-2 = k+5 := by omega
    have e3 : k+7-3 = k+4 := by omega
    have e4 : k+7-4 = k+3 := by omega
    have e5 : k+7-5 = k+2 := by omega
    have p0 : 0 ≤ k+7 := by omega
    have p1 : 1 ≤ k+7 := by omega
    have p2 : 2 ≤ k+7 := by omega
    have p3 : 3 ≤ k+7 := by omega
    have p4 : 4 ≤ k+7 := by omega
    have p5 : 5 ≤ k+7 := by omega
    have q1 : k+7 ≠ 1 := by omega
    have q2 : k+7 ≠ 2 := by omega
    have q3 : k+7 ≠ 3 := by omega
    have q4 : k+7 ≠ 4 := by omega
    have q5 : k+7 ≠ 5 := by omega
    have q6 : k+7 ≠ 6 := by omega
    simp only [if_pos p0,if_pos p1,if_pos p2,if_pos p3,if_pos p4,if_pos p5,
      if_neg q1,if_neg q2,if_neg q3,if_neg q4,if_neg q5,if_neg q6,Nat.sub_zero,e1,e2,e3,e4,e5]
    have h0 := closed (k+7) (by omega)
    have h1 := closed (k+6) (by omega)
    have h2 := closed (k+5) (by omega)
    have h3 := closed (k+4) (by omega)
    have h4 := closed (k+3) (by omega)
    have h5 := closed (k+2) (by omega)
    push_cast at h0 h1 h2 h3 h4 h5
    simp only [pow_add] at h0 h1 h2 h3 h4 h5
    norm_num at h0 h1 h2 h3 h4 h5 ⊢
    linarith only [h0,h1,h2,h3,h4,h5]

theorem OMA.solution : type_of% @OMA.S_oeis_a174655.main := ⟨closed,gf⟩
