import OMAReductions.R_Erdos499_vanDerWaerden_R1

-- Step Erdos499.vanDerWaerden.R1.H2: hypothesis H2 of reduction Erdos499.vanDerWaerden.R1
-- Credit: @marcusbuffett
-- H2 := ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ (v w : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ),     HasDerivAt       (fun t : ℝ =>         (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent)       ((k : ℝ) * (Matrix.of fun i j : Fin n =>         if (j : ℕ) + 1 < k then v i else if (j : ℕ) + 1 = k then w i else C i j).permanent)       0  /-- Univariate Gurvits inequality: if `f t = a * prod_{i<m} (t + r i)` with `a ≥ 0`, `r i ≥ 0`, `m ≤ d`, `d ≥ 1`, and `L * t ≤ f t` for all `t > 0`, then `((d-1)/d)^(d-1) * L ≤ f'(0)`. -/

open Matrix Finset

/-- Differentiate a permanent by replacing each column in turn by its derivative. -/
private theorem deriv_permanent {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) 0) :
    HasDerivAt (fun t => (A t).permanent) (∑ j, ((A 0).updateCol j (fun i => B i j)).permanent) 0 := by
  classical
  unfold Matrix.permanent
  rw [Finset.sum_comm]
  apply HasDerivAt.fun_sum
  intro σ _
  have d := HasDerivAt.fun_finsetProd (u := univ) (fun j _ => h (σ j) j)
  apply d.congr_deriv
  symm
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_prod_erase _ _ (mem_univ j), Matrix.updateCol_self, smul_eq_mul, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hr)

theorem OMA.solution : OMA.R_Erdos499_vanDerWaerden_R1.H2 := by
  intro n k hk hn v w C
  classical
  let A (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := of fun i j => if j.val < k then v i + t*w i else C i j
  let B : Matrix (Fin n) (Fin n) ℝ := of fun i j => if j.val < k then w i else 0
  let l : Fin n := ⟨k-1, by omega⟩
  have hl : l.val + 1 = k := by dsimp [l]; omega
  let M := (A 0).updateCol l w
  have hm : M = (Matrix.of fun i j : Fin n =>
        if (j : ℕ) + 1 < k then v i else if (j : ℕ) + 1 = k then w i else C i j) := by
    ext i j
    by_cases hj : j = l
    · subst j; simp [M, hl]
    · have hne : j.val ≠ l.val := fun e => hj (Fin.ext e)
      have hlt : j.val + 1 < k ↔ j.val < k := by omega
      have heq : j.val + 1 ≠ k := by omega
      simp [M, Matrix.updateCol_ne hj, A, hlt, heq]
  have hAB (i j) : HasDerivAt (fun t => A t i j) (B i j) 0 := by
    by_cases hj : (j : Fin n).val < k
    · simpa [A, B, hj] using ((hasDerivAt_id (0 : ℝ)).mul_const (w i)).const_add (v i)
    · simpa [A, B, hj] using hasDerivAt_const (0 : ℝ) (C i j)
  -- Swapping two of the first k columns identifies their derivative contributions.
  have term (j : Fin n) :
      ((A 0).updateCol j (fun i => B i j)).permanent = if j.val < k then M.permanent else 0 := by
    by_cases hj : j.val < k
    · rw [if_pos hj, ← Matrix.permanent_permute_rows (Equiv.swap l j) M]
      congr 1
      ext i r
      change (A 0).updateCol j (fun i => B i j) i r =
        (A 0).updateCol l w i (Equiv.swap l j r)
      by_cases h1 : r = j
      · subst r; simp [B, hj]
      · by_cases h2 : r = l
        · subst r
          simp [Matrix.updateCol_ne h1, Equiv.swap_apply_left, Matrix.updateCol_ne (Ne.symm h1), A, hj,
            show l.val < k by omega]
        · simp [Equiv.swap_apply_of_ne_of_ne h2 h1, Matrix.updateCol_ne h1, Matrix.updateCol_ne h2]
    · rw [if_neg hj]
      have hzero : (fun i => B i j) = (0 : ℝ) • w := by ext i; simp [B, hj]
      rw [hzero, Matrix.permanent_updateCol_smul, zero_mul]
  have d := deriv_permanent A B hAB
  simp_rw [term] at d
  rw [← Finset.sum_filter, Finset.sum_const, Fin.card_filter_val_lt, min_eq_right hn,
    nsmul_eq_mul, hm] at d
  exact d
