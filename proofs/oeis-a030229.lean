import OMAStatements.S_oeis_a030229

-- Problem oeis-a030229: for the divisibility matrix M (entry 1 when the column index divides the row index),
-- the statement claims that the inverse has entry -1 at (a, 1) for every squarefree a with an even number
-- of prime factors.
-- Upstream: statements/oeis-a030229.lean (declaration OMA.S_oeis_a030229.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- The statement is false. By Moebius inversion the entry is mu(a), which is +1 (not -1) on this set.
-- The smallest case already fails: a = 1 is in the set (zero prime factors), the truncation to N = 1 is
-- the 1 x 1 identity matrix, its inverse is the identity, and the entry is 1.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a030229.main) := by
  intro h
  have ha : (1 : ℕ) ∈ OMA.S_oeis_a030229.A030229 :=
    ⟨Nat.one_pos, squarefree_one, by simp⟩
  have h1 := h 1 1 ha le_rfl
  have hM : OMA.S_oeis_a030229.M 1 = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi
    subst hj
    simp [OMA.S_oeis_a030229.M]
  have hinv : (1 : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = 1 := Matrix.inv_eq_right_inv (one_mul 1)
  rw [hM, hinv] at h1
  norm_num [Matrix.one_apply] at h1
