import OMAStatements.S_oeis_a005043

open Polynomial OMA.S_oeis_a005043

lemma OMA.pasg (q : ℤ[X]) (k : ℕ) : (q * (1 + X + X ^ 2)).coeff k =
    q.coeff k + (if 1 ≤ k then q.coeff (k - 1) else 0) + (if 2 ≤ k then q.coeff (k - 2) else 0) := by
  rw [show q * (1 + X + X ^ 2) = q + q * X ^ 1 + q * X ^ 2 by ring, coeff_add, coeff_add,
    coeff_mul_X_pow', coeff_mul_X_pow']

lemma OMA.pasp (n k : ℕ) : ((1 + X + X ^ 2 : ℤ[X]) ^ (n + 1)).coeff k =
    ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k +
      (if 1 ≤ k then ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff (k - 1) else 0) +
      (if 2 ≤ k then ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff (k - 2) else 0) := by
  rw [pow_succ (1 + X + X ^ 2 : ℤ[X]) n]
  exact OMA.pasg _ k

lemma OMA.der (n k : ℕ) :
    ((1 + X + X ^ 2 : ℤ[X]) ^ (n + 1)).coeff (k + 1 + 1) * ((k : ℤ) + 1 + 1) =
      ((n : ℤ) + 1) * (((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff (k + 1) +
        2 * ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k) := by
  have h := congrArg (fun q : ℤ[X] => q.coeff (k + 1))
    (derivative_pow (1 + X + X ^ 2 : ℤ[X]) (n + 1))
  simp only [coeff_derivative, derivative_add, derivative_one, derivative_X, derivative_X_sq,
    zero_add, Nat.add_sub_cancel] at h
  rw [show (C ((n + 1 : ℕ) : ℤ) * (1 + X + X ^ 2 : ℤ[X]) ^ n * (1 + C 2 * X)) =
      C ((n + 1 : ℕ) : ℤ) * ((1 + X + X ^ 2 : ℤ[X]) ^ n + C 2 * ((1 + X + X ^ 2 : ℤ[X]) ^ n * X))
      by ring, coeff_C_mul, coeff_add, coeff_C_mul, coeff_mul_X] at h
  push_cast at h
  linarith

lemma OMA.alg (m : ℕ) (c0 b0 e0 c1 b1 e1 c2 b2 : ℤ)
    (A0 : c1 * (((m + 1 : ℕ) : ℤ) + 1 + 1) = (((m + 2 : ℕ) : ℤ) + 1) * (c0 + 2 * b0))
    (D0 : b1 * ((m : ℤ) + 1 + 1) = (((m + 2 : ℕ) : ℤ) + 1) * (b0 + 2 * e0))
    (P0 : b1 = c0 + b0 + e0)
    (A1 : c2 * (((m + 2 : ℕ) : ℤ) + 1 + 1) = (((m + 3 : ℕ) : ℤ) + 1) * (c1 + 2 * b1))
    (D1 : b2 * (((m + 1 : ℕ) : ℤ) + 1 + 1) = (((m + 3 : ℕ) : ℤ) + 1) * (b1 + 2 * e1))
    (P1 : b2 = c1 + b1 + e1) :
    (((m + 2 : ℕ) : ℚ) + 1) / (((m + 2 : ℕ) : ℚ) + 3) *
        (2 * ((c1 - b1 : ℤ) : ℚ) + 3 * ((c0 - b0 : ℤ) : ℚ)) = ((c2 - b2 : ℤ) : ℚ) := by
  push_cast at A0 D0 A1 D1
  have A1c : c2 = c1 + 2 * b1 := by
    have h : ((m : ℤ) + 4) ≠ 0 := by positivity
    apply mul_left_cancel₀ h
    linarith
  have G : ((m : ℤ) + 5) * (c2 - b2) = ((m : ℤ) + 3) * (2 * (c1 - b1) + 3 * (c0 - b0)) := by
    linear_combination ((m : ℤ) + 5) * A1c - (2 * ((m : ℤ) + 4) * P1 - D1) - 3 * A0 +
      3 * (2 * ((m : ℤ) + 3) * P0 - D0)
  have Gq : ((m : ℚ) + 5) * ((c2 - b2 : ℤ) : ℚ) =
      ((m : ℚ) + 3) * (2 * ((c1 - b1 : ℤ) : ℚ) + 3 * ((c0 - b0 : ℤ) : ℚ)) := by
    exact_mod_cast G
  have h5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  push_cast
  field_simp
  push_cast at Gq
  linarith

lemma OMA.core (t : ℕ → ℕ → ℤ)
    (pas : ∀ n k, t (n + 1) k = t n k + (if 1 ≤ k then t n (k - 1) else 0) +
      (if 2 ≤ k then t n (k - 2) else 0))
    (der : ∀ n k, t (n + 1) (k + 1 + 1) * ((k : ℤ) + 1 + 1) =
      ((n : ℤ) + 1) * (t n (k + 1) + 2 * t n k))
    (t0 : ∀ k, t 0 k = if k = 0 then 1 else 0) :
    ∀ n : ℕ, 0 < n → riordan n = ((t n n - t n (n - 1) : ℤ) : ℚ) := by
  have v10 : t 1 0 = 1 := by simp [pas, t0]
  have v11 : t 1 1 = 1 := by simp [pas, t0]
  have v21 : t 2 1 = 2 := by simp [pas, t0]
  have v22 : t 2 2 = 3 := by simp [pas, t0]
  have v32 : t 3 2 = 6 := by simp [pas, t0]
  have v33 : t 3 3 = 7 := by simp [pas, t0]
  have r1 : riordan 1 = 0 := by simp [riordan]
  have r2 : riordan 2 = 1 := by norm_num [riordan]
  have r3 : riordan 3 = 1 := by norm_num [riordan]
  have key : ∀ m : ℕ, riordan (m + 2) = ((t (m + 2) (m + 2) - t (m + 2) (m + 1) : ℤ) : ℚ) ∧
      riordan (m + 3) = ((t (m + 3) (m + 3) - t (m + 3) (m + 2) : ℤ) : ℚ) := by
    intro m
    induction m with
    | zero =>
      constructor
      · show riordan 2 = ((t 2 2 - t 2 1 : ℤ) : ℚ)
        rw [v22, v21, r2]
        norm_num
      · show riordan 3 = ((t 3 3 - t 3 2 : ℤ) : ℚ)
        rw [v33, v32, r3]
        norm_num
    | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨ih2, ?_⟩
      show riordan (m + 4) = ((t (m + 4) (m + 4) - t (m + 4) (m + 3) : ℤ) : ℚ)
      have hr : riordan (m + 2 + 2) = (((m + 2 : ℕ) : ℚ) + 1) / (((m + 2 : ℕ) : ℚ) + 3) *
          (2 * riordan (m + 2 + 1) + 3 * riordan (m + 2)) := by
        rw [riordan]
      have e3 : riordan (m + 2 + 1) = riordan (m + 3) := rfl
      have e4 : riordan (m + 2 + 2) = riordan (m + 4) := rfl
      have P0 : t (m + 3) (m + 2) = t (m + 2) (m + 2) + t (m + 2) (m + 1) + t (m + 2) m := by
        simpa using pas (m + 2) (m + 2)
      have P1 : t (m + 4) (m + 3) = t (m + 3) (m + 3) + t (m + 3) (m + 2) + t (m + 3) (m + 1) := by
        simpa using pas (m + 3) (m + 3)
      rw [← e4, hr, e3, ih1, ih2]
      exact OMA.alg m _ _ _ _ _ _ _ _ (der (m + 2) (m + 1)) (der (m + 2) m) P0
        (der (m + 3) (m + 2)) (der (m + 3) (m + 1)) P1
  intro n hn
  obtain ⟨m, rfl⟩ | rfl : (∃ m, n = m + 2) ∨ n = 1 := by
    rcases n with _ | _ | n
    · omega
    · right; rfl
    · left; exact ⟨n, rfl⟩
  · exact (key m).1
  · show riordan 1 = ((t 1 1 - t 1 0 : ℤ) : ℚ)
    rw [v11, v10, r1]
    norm_num

theorem OMA.solution : type_of% @OMA.S_oeis_a005043.main := by
  intro n hn
  have h := OMA.core (fun n k => ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k) OMA.pasp OMA.der
    (fun k => by simp [coeff_one]) n hn
  unfold trinomialCentral trinomialNext
  exact h
