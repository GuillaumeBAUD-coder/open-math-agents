import OMAStatements.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues

/-!
A disproof of the statement as formalized: the bound `2 * sqrt (d - 1)` is required for `d = 1` as well,
but it is then `0`, while a `1`-regular graph (a matching) has a symmetric signing whose eigenvalues are
`±1` in absolute value.

Concretely take `V = Fin 2`, `G = ⊤` (the single edge `{0, 1}`, which is `1`-regular) and any signing
`σ`. The signed adjacency matrix is `!![0, σ 0 1; σ 1 0, 0]`; by symmetry `σ 1 0 = σ 0 1` and by the
sign condition `σ 0 1 = ±1`, so its determinant is `-(σ 0 1)^2 = -1`. On the other hand a Hermitian
matrix has determinant the product of its eigenvalues, and every eigenvalue is required to satisfy
`|λ| ≤ 2 * sqrt (1 - 1) = 0`, so the product is `0`: a contradiction.

The conjectured statement is the Bilu–Linial signing conjecture, usually stated for `d ≥ 2` (or for the
nontrivial eigenvalues); the `d = 1` case admitted by this formalization is what fails here.
-/

open OMA.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues.main) := by
  intro hmain
  obtain ⟨σ, hsign, hsym, hHerm, hbound⟩ :=
    hmain (Fin 2) ⊤ 1 le_rfl (by simpa using (SimpleGraph.IsRegularOfDegree.top (V := Fin 2)))
  -- the signed adjacency matrix of the single edge
  have hA : signedAdj (⊤ : SimpleGraph (Fin 2)) σ = !![0, σ 0 1; σ 1 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [signedAdj]
  -- its determinant is `-1`
  have hdet : Matrix.det (signedAdj (⊤ : SimpleGraph (Fin 2)) σ) = -1 := by
    rw [hA, Matrix.det_fin_two_of]
    rw [hsym 1 0]
    rcases hsign 0 1 with h1 | h1 <;> rw [h1] <;> norm_num
  -- the bound forces every eigenvalue to vanish
  have hzero : ∀ i, hHerm.eigenvalues i = 0 := by
    intro i
    have hle : |hHerm.eigenvalues i| ≤ 0 := by simpa using hbound i
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  -- so the determinant, a product of eigenvalues, is zero
  have hd := hHerm.det_eq_prod_eigenvalues
  rw [hdet] at hd
  simp [hzero] at hd
