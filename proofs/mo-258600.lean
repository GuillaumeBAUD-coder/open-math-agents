import OMAStatements.S_mo_258600

-- Problem mo-258600: the statement claims that for every surjective ring homomorphism f : A -> B and every n > 1
-- the induced map GL_n(A) -> GL_n(B) is surjective.
-- Upstream: statements/mo-258600.lean (declaration OMA.S_mo_258600.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take A = Z, B = Z/5, f the reduction map and n = 2. The matrix diag(2, 1) is invertible over Z/5
-- (inverse diag(3, 1)) and has determinant 2. An invertible integer matrix has determinant 1 or -1, so its
-- reduction has determinant 1 or 4 in Z/5, never 2. Hence diag(2, 1) is not in the image.

open OMA.S_mo_258600

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_258600.main) := by
  intro h
  have hsurj := h ℤ (ZMod 5) (Int.castRingHom (ZMod 5)) (ZMod.ringHom_surjective _) 2 (by norm_num)
  have h1 : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 5)) * !![3, 0; 0, 1] = 1 := by decide
  have h2 : (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 5)) * !![2, 0; 0, 1] = 1 := by decide
  obtain ⟨M, hM⟩ := hsurj ⟨!![2, 0; 0, 1], !![3, 0; 0, 1], h1, h2⟩
  have hval : (Int.castRingHom (ZMod 5)).mapMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) = !![2, 0; 0, 1] :=
    congrArg Units.val hM
  have hdet : (Int.castRingHom (ZMod 5)) (M : Matrix (Fin 2) (Fin 2) ℤ).det = 2 := by
    rw [RingHom.map_det, hval, Matrix.det_fin_two_of]
    decide
  have hu : IsUnit (M : Matrix (Fin 2) (Fin 2) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
  rcases Int.isUnit_iff.mp hu with hc | hc
  · rw [hc] at hdet
    have h3 : (1 : ZMod 5) = 2 := by simpa using hdet
    exact absurd h3 (by decide)
  · rw [hc] at hdet
    have h3 : (-1 : ZMod 5) = 2 := by simpa using hdet
    exact absurd h3 (by decide)
