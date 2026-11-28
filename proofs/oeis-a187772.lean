import OMAStatements.S_oeis_a187772

open OMA.S_oeis_a187772 Nat

private def Q (k : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod k) := !![0, 1; 1, 1]

private theorem qp (k n : ℕ) :
    Q k ^ n = !![(fib (n+1) - fib n : ZMod k), fib n; fib n, fib (n+1)] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Q, Matrix.mul_apply, fib_add_two]

private theorem qe (k p : ℕ) : Q k ^ p = 1 ↔ ∀ r, fib (r + p) % k = fib r % k := by
  simp_rw [← ZMod.natCast_eq_natCast_iff']
  refine ⟨fun h r => ?_, fun h => ?_⟩
  · simpa [qp] using congrArg (· 0 1) (show Q k ^ (r + p) = Q k ^ r by rw [pow_add, h, mul_one])
  · have h0 := h 0; have h1 := h 1
    simp [add_comm 1] at h0 h1
    ext i j; fin_cases i <;> fin_cases j <;> simp [qp, h0, h1]

theorem OMA.solution : type_of% @OMA.S_oeis_a187772.main := by
  intro k hk
  have : NeZero k := ⟨by omega⟩
  have hp : 0 < orderOf (Q k) := (Matrix.isUnit_iff_isUnit_det _).2 (by simp [Q]) |>.isOfFinOrder.orderOf_pos
  have e : a187772 2 k = orderOf (Q k) := by
    have h₀ : matMod k (danzerMatrix 2 0) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matMod, danzerMatrix, chebSMat]
    have h₁ : matMod k (danzerMatrix 2 1) = Q k := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matMod, danzerMatrix, chebSMat, danzerBase, Q]
    simp [a187772, a220555, Finset.univ_fin2, h₀, h₁]; omega
  have hm : orderOf (Q k) ∈ {p | 0 < p ∧ ∀ r, fib (r + p) % k = fib r % k} := ⟨hp, (qe k _).1 (pow_orderOf_eq_one _)⟩
  have hs := Nat.sInf_mem ⟨_, hm⟩
  rw [e]
  exact le_antisymm (orderOf_le_of_pow_eq_one hs.1 ((qe k _).2 hs.2)) (Nat.sInf_le hm)
