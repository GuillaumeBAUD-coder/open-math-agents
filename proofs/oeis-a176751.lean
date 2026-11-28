import OMAStatements.S_oeis_a176751

/-! Proof. With `A = ∑ a(n) xⁿ`, the defining convolution gives a quadratic `P A² + Q A + R = 0`
with polynomial `P, Q, R`. Writing `B = 2PA + Q`, `B² = Q² - 4PR =: Δ` and differentiating gives
`2ΔB' = Δ'B`, a first-order linear ODE for `A`; after cancelling the factor `4*(x - 1)` its
coefficient of `x^n` is the stated recurrence (the inhomogeneous part has degree `< 4`). -/

namespace OMA.S_oeis_a176751
open PowerSeries

lemma len (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases n with _ | n
    · rfl
    · simp only [aList, List.length_append, List.length_singleton, ih]

lemma pre (n : ℕ) : ∀ k ≤ n, (aList n).getD k 0 = a k := by
  induction n with
  | zero => intro k hk; interval_cases k; rfl
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n+1) with h | h
    · rcases n with _ | n
      · interval_cases k; rfl
      · rw [← ih k (by omega)]
        simp only [aList]
        rw [List.getD_append _ _ _ _ (by rw [len]; omega)]
    · have : k = n + 1 := by omega
      subst this; rfl

lemma step (n : ℕ) : a (n+2) = (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) - 1 := by
  unfold a
  simp only [aList]
  rw [List.getD_append_right _ _ _ _ (by rw [len])]
  rw [len, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [Finset.mem_range] at hp
  rw [pre (n+1) p (by omega), pre (n+1) (n+1-p) (by omega)]; rfl

noncomputable def A : ℚ⟦X⟧ := mk fun n => (a n : ℚ)
noncomputable def U : ℚ⟦X⟧ := C (-1 : ℚ) * mk 1
noncomputable def PP : ℚ⟦X⟧ := (-(X * (1 - X)))
noncomputable def QQ : ℚ⟦X⟧ := (1 - X)
noncomputable def RR : ℚ⟦X⟧ := ((1 - X) * (X - 1 - C (5 : ℚ) * X) - C (-1 : ℚ) * X ^ 2)

lemma hE0 : A - 1 - (C (5 : ℚ) * X) + X - X * A ^ 2 = X ^ 2 * U := by
  ext m
  rcases m with _ | _ | m
  · simp [A, a, aList]
  · have k1 : coeff 1 A = (a 1 : ℚ) := by simp only [A, coeff_mk]
    have k2 : coeff 1 (1:ℚ⟦X⟧) = 0 := by simp [coeff_one]
    have k3 : coeff 1 ((C (5 : ℚ) * X)) = (5 : ℚ) := by simp [coeff_C_mul, coeff_X]
    have k4 : coeff 1 (X:ℚ⟦X⟧) = 1 := by simp [coeff_X]
    have k5 : coeff 1 (X * A ^ 2) = (a 0 : ℚ) ^ 2 := by
      rw [show (1:ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff, map_pow]
      simp [A]
    have k6 : coeff 1 (X ^ 2 * U) = 0 := by rw [coeff_X_pow_mul', if_neg (by omega)]
    have v0 : a 0 = 1 := rfl
    have v1 : a 1 = 5 := by simp [a, aList]
    rw [show (0:ℕ) + 1 = 1 from rfl, map_sub, map_add, map_sub, map_sub, k1, k2, k3, k4, k5, k6, v0, v1]
    push_cast; ring
  · rw [show m + 1 + 1 = m + 2 by ring]
    have l1 : coeff (m+2) A = (a (m+2) : ℚ) := by simp only [A, coeff_mk]
    have l2 : coeff (m+2) (1:ℚ⟦X⟧) = 0 := by simp [coeff_one]
    have l3 : coeff (m+2) ((C (5 : ℚ) * X)) = 0 := by simp [coeff_C_mul, coeff_X]
    have l4 : coeff (m+2) (X:ℚ⟦X⟧) = 0 := by simp [coeff_X]
    have l5 : coeff (m+2) (X * A ^ 2) = ∑ k ∈ Finset.range (m + 2), (a k : ℚ) * (a (m + 1 - k) : ℚ) := by
      rw [coeff_succ_X_mul, pow_two, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j A)]
      simp only [A, coeff_mk]
    have l6 : coeff (m+2) (X ^ 2 * U) = (-1 : ℚ) := by
      rw [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]; simp [U]
    rw [map_sub, map_add, map_sub, map_sub, l1, l2, l3, l4, l5, l6, step m]
    push_cast
    ring

lemma hU : (1 - X : ℚ⟦X⟧) * U = (-1 : ℚ⟦X⟧) := by
  unfold U
  have h' : (1 - X : ℚ⟦X⟧) * mk 1 = 1 := by
    rw [mul_comm]; exact mk_one_mul_one_sub_eq_one ℚ
  try exact h'
  rw [← mul_assoc, mul_right_comm (1 - X), h']
  simp [one_mul, map_neg, map_one]

lemma dPP : d⁄dX ℚ PP = (2*X - 1) := by
  unfold PP
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat, derivative_X, derivative_C,
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
  ring

lemma dQQ : d⁄dX ℚ QQ = (-1) := by
  unfold QQ
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat, derivative_X, derivative_C,
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
  ring

lemma dRR : d⁄dX ℚ RR = (10*X - 3) := by
  unfold RR
  simp only [map_add, map_sub, map_mul, map_neg, map_one, derivative_X, derivative_C,
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
  simp only [map_ofNat, map_natCast, map_neg, map_one, map_zero]
  ring

lemma hE : PP * A ^ 2 + QQ * A + RR = 0 := by
  have h0 := hE0
  unfold PP QQ RR
  simp only [map_ofNat, map_natCast, map_neg, map_one, map_zero] at h0 ⊢
  linear_combination (1 - X) * h0 + X ^ 2 * hU

lemma hE' : d⁄dX ℚ PP * A ^ 2 + PP * (2 * A * d⁄dX ℚ A) + d⁄dX ℚ QQ * A + QQ * d⁄dX ℚ A + d⁄dX ℚ RR = 0 := by
  have h := congrArg (d⁄dX ℚ) hE
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_zero,
    smul_eq_mul, nsmul_eq_mul, Nat.add_one_sub_one, pow_one] at h
  linear_combination h

lemma hZ : (-20*X^5 + 32*X^4 - 7*X^3 - 6*X^2 + X) * d⁄dX ℚ A + (-4*X^3 + 5*X^2 - 4*X + 1) * A + (-10*X^3 + 18*X^2 - 6*X - 1) = 0 := by
  have hg : (4 * (X - 1) : ℚ⟦X⟧) * ((-20*X^5 + 32*X^4 - 7*X^3 - 6*X^2 + X) * d⁄dX ℚ A + (-4*X^3 + 5*X^2 - 4*X + 1) * A + (-10*X^3 + 18*X^2 - 6*X - 1)) = 0 := by
    have hE0' := hE
    have hE1 := hE'
    rw [dPP, dQQ, dRR] at hE1
    unfold PP QQ at hE1
    unfold PP QQ RR at hE0'
    simp only [map_ofNat, map_natCast, map_neg, map_one, map_zero] at hE0' hE1
    linear_combination ((-16*A*X^3 + 24*A*X^2 - 8*A*X - 16*(d⁄dX ℚ A)*X^4 + 32*(d⁄dX ℚ A)*X^3 - 16*(d⁄dX ℚ A)*X^2 + 4*X - 4)) * hE0' + ((8*A*X^4 - 16*A*X^3 + 8*A*X^2 - 4*X^3 + 8*X^2 - 4*X)) * hE1
  have hgn : (4 * (X - 1) : ℚ⟦X⟧) ≠ 0 := by
    intro h4
    apply_fun (constantCoeff : ℚ⟦X⟧ → ℚ) at h4
    norm_num [map_mul, map_sub, map_one, map_ofNat] at h4
  exact (mul_eq_zero.mp hg).resolve_left hgn

lemma cX (Y : ℚ⟦X⟧) (j e : ℕ) : coeff (e + j) (X ^ j * Y) = coeff e Y := by
  rw [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]

lemma cA (j e : ℕ) : coeff (e + j) (X ^ j * A) = (a e : ℚ) := by
  rw [cX, A, coeff_mk]

lemma cdA (j e : ℕ) : coeff (e + j) (X ^ j * d⁄dX ℚ A) = ((e:ℚ) + 1) * (a (e+1) : ℚ) := by
  rw [cX, coeff_derivative, A, coeff_mk]; ring

lemma cdA0 (s e : ℕ) : coeff (e + s) (X ^ (s+1) * d⁄dX ℚ A) = (e:ℚ) * (a e : ℚ) := by
  rcases e with _ | e
  · rw [coeff_X_pow_mul', if_neg (by omega)]; simp
  · rw [show e + 1 + s = e + (s + 1) by ring, cX, coeff_derivative, A, coeff_mk]; push_cast; ring

lemma cR (j m : ℕ) (h : j < m) : coeff m (X ^ j : ℚ⟦X⟧) = 0 := by
  rw [coeff_X_pow, if_neg (by omega)]

theorem solution_main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (1 - 3 * (n : ℤ)) * a (n - 1)
      + (19 - 7 * (n : ℤ)) * a (n - 2)
      + 4 * (8 * (n : ℤ) - 25) * a (n - 3)
      + 20 * (4 - (n : ℤ)) * a (n - 4) = 0 := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by omega⟩
  simp only [show N + 4 - 1 = N + 3 by omega, show N + 4 - 2 = N + 2 by omega, show N + 4 - 3 = N + 1 by omega, show N + 4 - 4 = N + 0 by omega]
  set dA := d⁄dX ℚ A
  have e : (-20*X^5 + 32*X^4 - 7*X^3 - 6*X^2 + X) * dA + (-4*X^3 + 5*X^2 - 4*X + 1) * A + (-10*X^3 + 18*X^2 - 6*X - 1) = C (1 : ℚ) * (X ^ 1 * dA) + C (-6 : ℚ) * (X ^ 2 * dA) + C (-7 : ℚ) * (X ^ 3 * dA) + C (32 : ℚ) * (X ^ 4 * dA) + C (-20 : ℚ) * (X ^ 5 * dA) + C (1 : ℚ) * (X ^ 0 * A) + C (-4 : ℚ) * (X ^ 1 * A) + C (5 : ℚ) * (X ^ 2 * A) + C (-4 : ℚ) * (X ^ 3 * A) + C (-1 : ℚ) * X ^ 0 + C (-6 : ℚ) * X ^ 1 + C (18 : ℚ) * X ^ 2 + C (-10 : ℚ) * X ^ 3 := by
    simp only [map_ofNat, map_neg, map_one, map_zero, map_div₀]; ring
  have h := congrArg (coeff (N+4)) hZ
  rw [e] at h
  simp only [map_add, map_zero, coeff_C_mul] at h
  have p1 : coeff (N+4) (X ^ 1 * dA) = ((N+3:ℕ)+1:ℚ) * (a (N+3+1) : ℚ) := cdA 1 (N+3)
  have p2 : coeff (N+4) (X ^ 2 * dA) = ((N+2:ℕ)+1:ℚ) * (a (N+2+1) : ℚ) := cdA 2 (N+2)
  have p3 : coeff (N+4) (X ^ 3 * dA) = ((N+1:ℕ)+1:ℚ) * (a (N+1+1) : ℚ) := cdA 3 (N+1)
  have p4 : coeff (N+4) (X ^ 4 * dA) = ((N+0:ℕ)+1:ℚ) * (a (N+0+1) : ℚ) := cdA 4 (N+0)
  have p5 : coeff (N+4) (X ^ 5 * dA) = (N:ℚ) * (a N : ℚ) := cdA0 4 N
  have q0 : coeff (N+4) (X ^ 0 * A) = (a (N+4) : ℚ) := cA 0 (N+4)
  have q1 : coeff (N+4) (X ^ 1 * A) = (a (N+3) : ℚ) := cA 1 (N+3)
  have q2 : coeff (N+4) (X ^ 2 * A) = (a (N+2) : ℚ) := cA 2 (N+2)
  have q3 : coeff (N+4) (X ^ 3 * A) = (a (N+1) : ℚ) := cA 3 (N+1)
  have r0 : coeff (N+4) (X ^ 0 : ℚ⟦X⟧) = 0 := cR 0 (N+4) (by omega)
  have r1 : coeff (N+4) (X ^ 1 : ℚ⟦X⟧) = 0 := cR 1 (N+4) (by omega)
  have r2 : coeff (N+4) (X ^ 2 : ℚ⟦X⟧) = 0 := cR 2 (N+4) (by omega)
  have r3 : coeff (N+4) (X ^ 3 : ℚ⟦X⟧) = 0 := cR 3 (N+4) (by omega)
  rw [p1, p2, p3, p4, p5, q0, q1, q2, q3, r0, r1, r2, r3] at h
  qify
  push_cast at h ⊢
  linear_combination (1) * h

end OMA.S_oeis_a176751

theorem OMA.solution : type_of% @OMA.S_oeis_a176751.main := OMA.S_oeis_a176751.solution_main

