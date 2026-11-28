import OMAReductions.R_LatinSquare_oddOrderLatinSquareTransversal_R1

/-!
# Proof of `LatinSquare.oddOrderLatinSquareTransversal.R1.H1`

Any Latin square of odd order isotopic to the Cayley table of a group `G` has a transversal:
in a finite group of odd order `2 * k + 1`, squaring `x ↦ x * x` is injective because
`(x * x) ^ (k + 1) = x ^ |G| * x = x`, so `σ i = β⁻¹ (α i)` yields a transversal.
-/

-- Step LatinSquare.oddOrderLatinSquareTransversal.R1.H1: hypothesis H1 of reduction LatinSquare.oddOrderLatinSquareTransversal.R1
-- Credit: @LiJiaHua1024

theorem OMA.solution : OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R1.H1 := by
  rintro n ⟨k, rfl⟩ L ⟨G, hG, α, β, γ, hL⟩
  let _ : Group G := hG
  let _ : Fintype G := Fintype.ofEquiv (Fin (2 * k + 1)) α
  have hcard : Fintype.card G = 2 * k + 1 := by
    rw [Fintype.card_congr α.symm, Fintype.card_fin]
  have hsq_inj : Function.Injective (fun x : G => x * x) := by
    intro x y hxy
    dsimp only at hxy
    have hpow : ∀ z : G, (z * z) ^ (k + 1) = z := fun z => by
      have h1 : z * z = z ^ 2 := (sq z).symm
      rw [h1, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hcard,
        pow_card_eq_one, one_mul]
    rw [← hpow x, ← hpow y, hxy]
  refine ⟨fun i => β.symm (α i), β.symm.injective.comp α.injective, ?_⟩
  intro i j hij
  simp only [hL, Equiv.apply_symm_apply] at hij
  exact α.injective (hsq_inj (γ.injective hij))
