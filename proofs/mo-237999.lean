import OMAStatements.S_mo_237999

/-!
# Disproof of MathOverflow 237999 as stated in the catalogue

The question asks whether every real matrix that is weakly diagonally dominant, has zero row sums
and admits no decoupling `A = R * diag(B, C) * Rᵀ` is positive semi-definite.

The matrix `A = !![(-1 : ℝ), 1; 1/2, -(1/2)]` is a counterexample.  Its rows sum to zero and it is
weakly diagonally dominant, but it is not positive semi-definite: on the vector `![1, -1]` the
quadratic form equals `-3`.

The third hypothesis is vacuous for this `A`: a decoupling `A = R * D * Rᵀ` forces `A` to be
symmetric, because for a nonempty proper subset `S` of `Fin 2` the condition
`∀ i j, (i ∈ S ↔ j ∉ S) → D i j = 0` gives `D 0 1 = 0 = D 1 0`, so that `Dᵀ = D` and hence
`Aᵀ = R * Dᵀ * Rᵀ = A`; but `A 0 1 = 1` while `A 1 0 = 1/2`.
-/

open Matrix

/-- In `Fin 2`, membership in a nonempty proper subset separates the two points. -/
private lemma md1_sep0 (S : Finset (Fin 2)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ((0 : Fin 2) ∈ S ↔ (1 : Fin 2) ∉ S) := by
  by_cases h0 : (0 : Fin 2) ∈ S
  · have h1not : (1 : Fin 2) ∉ S := by
      intro h1
      apply hproper
      apply Finset.eq_univ_of_forall
      intro x
      fin_cases x
      · exact h0
      · exact h1
    exact ⟨fun _ => h1not, fun _ => h0⟩
  · have h1mem : (1 : Fin 2) ∈ S := by
      obtain ⟨x, hx⟩ := hne
      fin_cases x
      · exact absurd hx h0
      · assumption
    exact ⟨fun h => absurd h h0, fun h => absurd h1mem h⟩

/-- The companion statement for the other point of `Fin 2`. -/
private lemma md1_sep1 (S : Finset (Fin 2)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ((1 : Fin 2) ∈ S ↔ (0 : Fin 2) ∉ S) := by
  by_cases h1 : (1 : Fin 2) ∈ S
  · have h0not : (0 : Fin 2) ∉ S := by
      intro h0
      apply hproper
      apply Finset.eq_univ_of_forall
      intro x
      fin_cases x
      · exact h0
      · exact h1
    exact ⟨fun _ => h0not, fun _ => h1⟩
  · have h0mem : (0 : Fin 2) ∈ S := by
      obtain ⟨x, hx⟩ := hne
      fin_cases x
      · assumption
      · exact absurd hx h1
    exact ⟨fun h => absurd h h1, fun h => absurd h0mem h⟩

/-- A nonempty proper subset of `Fin 2` forces such a `D` to be symmetric. -/
private lemma md1_Dsym (D : Matrix (Fin 2) (Fin 2) ℝ) (S : Finset (Fin 2)) (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) (hzero : ∀ i j, (i ∈ S ↔ j ∉ S) → D i j = 0) : Dᵀ = D := by
  have h0 := md1_sep0 S hne hproper
  have h1 := md1_sep1 S hne hproper
  have e : D 1 0 = D 0 1 := by rw [hzero 1 0 h1, hzero 0 1 h0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, e]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_237999.main) := by
  intro h
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![(-1 : ℝ), 1; (1/2 : ℝ), -(1/2)] with hAdef
  have hrow : ∀ i, ∑ j, A i j = 0 := by
    intro i
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with rfl | rfl <;> simp [hAdef, Fin.sum_univ_two]
  have hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i| := by
    intro i
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with rfl | rfl
    · have he : Finset.univ.erase (0 : Fin 2) = ({1} : Finset (Fin 2)) := by decide
      rw [he]
      simp [hAdef]
    · have he : Finset.univ.erase (1 : Fin 2) = ({0} : Finset (Fin 2)) := by decide
      rw [he]
      simp [hAdef]
  have hnodec : ¬ ∃ (R D : Matrix (Fin 2) (Fin 2) ℝ) (S : Finset (Fin 2)), IsUnit R ∧ S.Nonempty ∧
      S ≠ Finset.univ ∧ (∀ i j, (i ∈ S ↔ j ∉ S) → D i j = 0) ∧ A = R * D * Rᵀ := by
    rintro ⟨R, D, S, -, hne, hproper, hzero, hAeq⟩
    have hsym : Dᵀ = D := md1_Dsym D S hne hproper hzero
    have hAsymm : Aᵀ = A := by
      rw [hAeq]
      simp [Matrix.transpose_mul, hsym, Matrix.mul_assoc]
    have h12 : (1 / 2 : ℝ) = 1 := by
      have h' := congrFun (congrFun hAsymm 0) 1
      simp [Matrix.transpose_apply, hAdef] at h'
    norm_num at h12
  have hquad := h 2 A hrow hdom hnodec (![1, -1] : Fin 2 → ℝ)
  simp [dotProduct, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, hAdef] at hquad
  norm_num at hquad
