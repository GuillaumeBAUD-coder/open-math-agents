import OMAReductions.R_wp_nagata_s_conjecture_on_curves_R1

-- Step wp-nagata-s-conjecture-on-curves.R1.H1: hypothesis H1 of reduction wp-nagata-s-conjecture-on-curves.R1
-- Credit: @jaredwilder
-- H1 := ∀ {r : ℕ} (E : ℕ → MvPolynomial (Fin r × Fin 2) ℂ), (∀ n, E n ≠ 0) → ∃ p, outside E p

theorem OMA.nagata_dense_nonzero {σ : Type} [Fintype σ] (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    Dense {x : σ → ℂ | MvPolynomial.eval x P ≠ 0} := by
  have hc : {x : σ → ℂ | MvPolynomial.eval x P ≠ 0} = {x | MvPolynomial.eval x P = 0}ᶜ := rfl
  rw [hc, ← interior_eq_empty_iff_dense_compl]
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, hε, hsub⟩ := hx
  apply hP
  apply MvPolynomial.funext_set (fun i => Metric.ball (x i) ε)
  · intro i
    exact infinite_of_mem_nhds (x i) (Metric.ball_mem_nhds (x i) hε)
  · intro y hy
    have hy' : y ∈ Metric.ball x ε := by
      rw [ball_pi x hε]
      exact hy
    have := hsub hy'
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at this
    simp [this]

theorem OMA.solution : OMA.R_wp_nagata_s_conjecture_on_curves_R1.H1 := by
  unfold OMA.R_wp_nagata_s_conjecture_on_curves_R1.H1
  intro r E hE
  classical
  let D : MvPolynomial (Fin r × Fin 2) ℂ :=
    ∏ ij ∈ (Finset.univ.filter (fun ij : Fin r × Fin r => ij.1 ≠ ij.2)),
      (MvPolynomial.X (ij.1, 0) - MvPolynomial.X (ij.2, 0))
  have hD : D ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ij hij
    rw [Finset.mem_filter] at hij
    rw [sub_ne_zero]
    intro h
    apply hij.2
    have := MvPolynomial.X_injective h
    exact congrArg Prod.fst this
  let G : ℕ → MvPolynomial (Fin r × Fin 2) ℂ := fun n => Nat.casesOn n D E
  have hG : ∀ n, G n ≠ 0 := by
    intro n
    cases n with
    | zero => exact hD
    | succ n => exact hE n
  have hdense : Dense (⋂ n, {x : Fin r × Fin 2 → ℂ | MvPolynomial.eval x (G n) ≠ 0}) := by
    apply dense_iInter_of_isOpen
    · intro n
      exact isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    · intro n
      exact OMA.nagata_dense_nonzero _ (hG n)
  obtain ⟨x, hx⟩ := hdense.nonempty
  rw [Set.mem_iInter] at hx
  refine ⟨fun i j => x (i, j), ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have h0 : MvPolynomial.eval x D ≠ 0 := hx 0
    rw [map_prod, Finset.prod_ne_zero_iff] at h0
    have := h0 (i, j) (by simp [hne])
    simp only [map_sub, MvPolynomial.eval_X] at this
    apply this
    have := congrFun hij 0
    exact sub_eq_zero.mpr (by simpa using this)
  · intro n
    have := hx (n + 1)
    simpa [G] using this
