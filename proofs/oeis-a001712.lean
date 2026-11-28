import OMAStatements.S_oeis_a001712

/-!
# The recurrence for generalized Stirling numbers A001712

Source: https://oeis.org/A001712
Credit: @yakataN

The recurrence was proposed by Mathar in 2018 and proved in the OEIS entry
by Hadjicostas in 2020. This proof uses the second Taylor coefficient at 3
of the rising-factorial polynomial, then eliminates its lower coefficients.
-/

open Polynomial OMA.S_oeis_a001712
namespace A1712Proof

lemma poch_coeff (n k : ℕ) :
    (ascPochhammer ℤ n).coeff k = (Nat.stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero => cases k <;> simp [coeff_one]
  | succ n ih =>
    rw [ascPochhammer_succ_right, mul_add]
    cases k with
    | zero => cases n <;> simp [ih]
    | succ k =>
      simp only [coeff_add, coeff_mul_X, ← C_eq_natCast, coeff_mul_C, ih,
        Nat.stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul]
      ring

noncomputable def P (n : ℕ) : ℤ[X] := taylor 3 (ascPochhammer ℤ n)

lemma P_succ (n : ℕ) : P (n+1) = P n * (X + C ((n : ℤ) + 3)) := by
  simp only [P, ascPochhammer_succ_right, taylor_mul, map_add, taylor_X,
    ← C_eq_natCast, taylor_C]
  ring

lemma P_coeff_succ (n k : ℕ) :
    (P (n+1)).coeff (k+1) = (P n).coeff k + ((n : ℤ)+3) * (P n).coeff (k+1) := by
  rw [P_succ, mul_add, coeff_add, coeff_mul_X, coeff_mul_C]
  ring

lemma P_coeff_zero (n : ℕ) :
    (P (n+1)).coeff 0 = ((n : ℤ)+3) * (P n).coeff 0 := by
  rw [P_succ, mul_add, coeff_add, coeff_mul_X_zero, coeff_mul_C]
  ring

lemma a_eq (n : ℕ) : a n = (P (n+2)).coeff 2 := by
  have hd : (hasseDeriv 2 (ascPochhammer ℤ (n+2))).natDegree < n+1 := by
    have h := natDegree_hasseDeriv_le (ascPochhammer ℤ (n+2)) 2
    rw [ascPochhammer_natDegree] at h
    omega
  rw [P, taylor_coeff, eval_eq_sum_range' hd]
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  rw [hasseDeriv_coeff, poch_coeff]
  have hs : (-1 : ℤ) ^ (n+k) * (-1) ^ ((n+2)+(k+2)) = 1 := by
    rw [← pow_add, show n+k+((n+2)+(k+2)) = 2*(n+k+2) by omega, pow_mul]
    norm_num
  unfold s
  calc
    _ = ((-1 : ℤ) ^ (n+k) * (-1) ^ ((n+2)+(k+2))) *
        ((Nat.choose (k+2) 2 : ℤ) * (Nat.stirlingFirst (n+2) (k+2) : ℤ) * 3^k) := by ring
    _ = _ := by rw [hs]; ring

lemma recurrence (n : ℕ) :
    a (n+3) + 3 * (-((n : ℤ)+3)-3) * a (n+2) +
      (3*((n : ℤ)+3)^2+15*((n : ℤ)+3)+19)*a (n+1) -
      ((n : ℤ)+3+2)^3*a n = 0 := by
  simp only [a_eq]
  have f0 := P_coeff_succ (n+2) 1
  have f1 := P_coeff_succ (n+3) 1
  have f2 := P_coeff_succ (n+4) 1
  have g0 := P_coeff_succ (n+2) 0
  have g1 := P_coeff_succ (n+3) 0
  have h0 := P_coeff_zero (n+2)
  simp only [Nat.cast_add, Nat.cast_ofNat] at f0 f1 f2 g0 g1 h0
  linear_combination f2 + g1 + h0 - ((n : ℤ)+5)*g0 -
    (2*((n : ℤ)+5)+1)*f1 + ((n : ℤ)+5)^2*f0

end A1712Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a001712.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m+3 := ⟨n-3, by omega⟩
  simpa only [show m+3-1 = m+2 by omega, show m+3-2 = m+1 by omega,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat] using A1712Proof.recurrence m
