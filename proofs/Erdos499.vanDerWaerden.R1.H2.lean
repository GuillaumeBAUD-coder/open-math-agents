import OMAReductions.R_Erdos499_vanDerWaerden_R1

-- Step Erdos499.vanDerWaerden.R1.H2: hypothesis H2 of reduction Erdos499.vanDerWaerden.R1
-- Credit: @michielkosters
-- H2 := ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ (v w : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ),     HasDerivAt       (fun t : ℝ =>         (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent)       ((k : ℝ) * (Matrix.of fun i j : Fin n =>         if (j : ℕ) + 1 < k then v i else if (j : ℕ) + 1 = k then w i else C i j).permanent)       0  /-- Univariate Gurvits inequality: if `f t = a * prod_{i<m} (t + r i)` with `a ≥ 0`, `r i ≥ 0`, `m ≤ d`, `d ≥ 1`, and `L * t ≤ f t` for all `t > 0`, then `((d-1)/d)^(d-1) * L ≤ f'(0)`. -/

theorem OMA.solution : OMA.R_Erdos499_vanDerWaerden_R1.H2 := by
  intro n k hk1 hkn v w C
  let j₁ : Fin n := ⟨k - 1, by omega⟩
  have hj₁_lt : (j₁ : ℕ) < k := by simp [j₁]; omega
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j : Fin n =>
    if (j : ℕ) + 1 < k then v i else if (j : ℕ) + 1 = k then w i else C i j
  have hA : ∀ (σ : Equiv.Perm (Fin n)) (j : Fin n),
      (if (j : ℕ) + 1 < k then v (σ j) else if (j : ℕ) + 1 = k then w (σ j) else C (σ j) j) =
      (if j = j₁ then w (σ j) else if (j : ℕ) < k then v (σ j) else C (σ j) j) := by
    intro σ j
    by_cases hj1 : j = j₁
    · subst hj1
      have h2 : k - 1 + 1 = k := by omega
      simp [j₁, h2]
    · have hne : (j : ℕ) ≠ k - 1 := fun h => hj1 (Fin.ext h)
      by_cases hjk : (j : ℕ) < k
      · have h1 : (j : ℕ) + 1 < k := by omega
        simp [hj1, hjk, h1]
      · have h1 : ¬ ((j : ℕ) + 1 < k) := by omega
        have h2 : ¬ ((j : ℕ) + 1 = k) := by omega
        simp [hj1, hjk, h1, h2]
  have hfactor : ∀ (σ : Equiv.Perm (Fin n)) (j : Fin n),
      HasDerivAt (fun t : ℝ => if (j : ℕ) < k then v (σ j) + t * w (σ j) else C (σ j) j)
        (if (j : ℕ) < k then w (σ j) else 0) 0 := by
    intro σ j
    by_cases hj : (j : ℕ) < k
    · simp only [hj, ↓reduceIte]
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (w (σ j))).const_add (v (σ j))
      rw [one_mul] at h
      exact h
    · simp only [hj, ↓reduceIte]
      exact hasDerivAt_const (0 : ℝ) (C (σ j) j)
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      HasDerivAt
        (fun t : ℝ => ∏ j : Fin n, (if (j : ℕ) < k then v (σ j) + t * w (σ j) else C (σ j) j))
        (∑ j₀ : Fin n, if (j₀ : ℕ) < k then
          ∏ j : Fin n, (if j = j₀ then w (σ j) else if (j : ℕ) < k then v (σ j) else C (σ j) j)
          else 0)
        0 := by
    intro σ
    have hd := HasDerivAt.finsetProd
      (fun (j : Fin n) (_ : j ∈ (Finset.univ : Finset (Fin n))) => hfactor σ j)
    have hfun : (∏ j : Fin n, fun t : ℝ =>
          if (j : ℕ) < k then v (σ j) + t * w (σ j) else C (σ j) j) =
        (fun t : ℝ => ∏ j : Fin n, if (j : ℕ) < k then v (σ j) + t * w (σ j) else C (σ j) j) := by
      ext t; simp
    have hder : (∑ j₀ : Fin n,
          (∏ j ∈ Finset.univ.erase j₀, if (j : ℕ) < k then v (σ j) + 0 * w (σ j) else C (σ j) j) •
            if (j₀ : ℕ) < k then w (σ j₀) else 0) =
        (∑ j₀ : Fin n, if (j₀ : ℕ) < k then
          ∏ j : Fin n, (if j = j₀ then w (σ j) else if (j : ℕ) < k then v (σ j) else C (σ j) j)
          else 0) := by
      refine Finset.sum_congr rfl fun j₀ _ => ?_
      by_cases hj0 : (j₀ : ℕ) < k
      · simp only [hj0, ↓reduceIte, smul_eq_mul]
        rw [mul_comm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
        simp only [↓reduceIte]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        have hne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
        simp [hne]
      · simp [hj0]
    rw [hfun, hder] at hd
    exact hd
  have hsum : HasDerivAt
      (fun t : ℝ =>
        (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent)
      (∑ σ : Equiv.Perm (Fin n), ∑ j₀ : Fin n, if (j₀ : ℕ) < k then
        ∏ j : Fin n, (if j = j₀ then w (σ j) else if (j : ℕ) < k then v (σ j) else C (σ j) j)
        else 0)
      0 := by
    have hd := HasDerivAt.sum
      (fun (σ : Equiv.Perm (Fin n)) (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n)))) => hprod σ)
    have hfun : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), fun t : ℝ =>
          ∏ j : Fin n, if (j : ℕ) < k then v (σ j) + t * w (σ j) else C (σ j) j) =
        (fun t : ℝ =>
          (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent) := by
      ext t
      simp [Matrix.permanent, Matrix.of_apply]
    rw [hfun] at hd
    exact hd
  convert hsum using 1
  rw [Finset.sum_comm]
  have hinner : ∀ j₀ : Fin n, (j₀ : ℕ) < k →
      (∑ σ : Equiv.Perm (Fin n),
        ∏ j : Fin n, (if j = j₀ then w (σ j) else if (j : ℕ) < k then v (σ j) else C (σ j) j))
      = A.permanent := by
    intro j₀ hj0
    let τ : Equiv.Perm (Fin n) := Equiv.swap j₀ j₁
    have hperm : A.permanent = ∑ σ : Equiv.Perm (Fin n),
        ∏ j : Fin n, (if j = j₁ then w (σ j) else if (j : ℕ) < k then v (σ j) else C (σ j) j) := by
      simp only [A, Matrix.permanent, Matrix.of_apply]
      refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun j _ => hA σ j
    rw [hperm, ← Equiv.sum_comp (Equiv.mulRight τ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    symm
    rw [← Equiv.prod_comp τ]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hττ : (σ * τ) (τ j) = σ j := by
      change σ (τ (τ j)) = σ j
      simp [τ]
    have hlt : (τ j : ℕ) < k ↔ (j : ℕ) < k := by
      by_cases h0 : j = j₀
      · subst h0; simp [τ, hj0, hj₁_lt]
      · by_cases h1 : j = j₁
        · subst h1; simp [τ, hj0, hj₁_lt]
        · simp [τ, Equiv.swap_apply_of_ne_of_ne h0 h1]
    have heq1 : τ j = j₁ ↔ j = j₀ :=
      ⟨fun h => by simpa [τ] using congrArg τ h, fun h => by simp [τ, h]⟩
    by_cases h0 : j = j₀
    · subst h0
      simp [heq1]
    · have hneq1 : τ j ≠ j₁ := fun h => h0 (heq1.mp h)
      simp only [h0, hneq1, ↓reduceIte, hlt]
      by_cases hjk : (j : ℕ) < k
      · simp [hjk]
      · have h1 : j ≠ j₁ := fun h => hjk (h ▸ hj₁_lt)
        have hτj : τ j = j := Equiv.swap_apply_of_ne_of_ne h0 h1
        simp [hjk, hτj]
  calc (k : ℝ) * A.permanent
      = ((Finset.univ.filter (fun j₀ : Fin n => (j₀ : ℕ) < k)).card : ℝ) * A.permanent := by
        congr 2
        symm
        refine Eq.trans ?_ (Fintype.card_fin k)
        exact Finset.card_bij
          (fun (j₀ : Fin n) hj => ⟨j₀.1, (Finset.mem_filter.mp hj).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (Fin.val : Fin k → ℕ) h))
          (fun b _ => ⟨⟨b.1, lt_of_lt_of_le b.2 hkn⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, rfl⟩)
    _ = ∑ j₀ ∈ Finset.univ.filter (fun j₀ : Fin n => (j₀ : ℕ) < k), A.permanent := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ j₀ : Fin n, (if (j₀ : ℕ) < k then A.permanent else 0) := by
        rw [Finset.sum_filter]
    _ = ∑ j₀ : Fin n, ∑ σ : Equiv.Perm (Fin n), (if (j₀ : ℕ) < k then
          ∏ j : Fin n, (if j = j₀ then w (σ j) else if (j : ℕ) < k then v (σ j) else C (σ j) j)
          else 0) := by
        refine Finset.sum_congr rfl fun j₀ _ => ?_
        by_cases hj0 : (j₀ : ℕ) < k
        · simp [hj0, hinner j₀ hj0]
        · simp [hj0]
