import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1
import Mathlib

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H1: hypothesis H1 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1
-- Credit: @ivillar
--
-- For odd n, the squares L(i, j) = i + j and M(i, j) = 2 i + j over Fin n (arithmetic mod n) are
-- Latin (2 is invertible mod n) and orthogonal, since (2 i + j) - (i + j) = i recovers i.

open Fin.CommRing

namespace OMA.Erdos724H1

lemma two_inv (j : ℕ) : (2 : Fin (2 * j + 1 + 1 + 1)) * ((j + 2 : ℕ) : Fin (2 * j + 1 + 1 + 1)) = 1 := by
  have h : ((2 * (j + 2) : ℕ) : Fin (2 * j + 1 + 1 + 1)) = 1 := by
    have : 2 * (j + 2) = (2 * j + 1 + 1 + 1) + 1 := by ring
    rw [this, Nat.cast_add, Fin.natCast_self, zero_add, Nat.cast_one]
  rw [← h]
  push_cast
  rfl

end OMA.Erdos724H1

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1 := by
  unfold OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1
  intro n hodd h3
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 + 1 + 1 := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m - 1, by omega⟩
  set t : Fin (2 * j + 1 + 1 + 1) := ((j + 2 : ℕ) : Fin (2 * j + 1 + 1 + 1)) with ht
  have h2 : (2 : Fin (2 * j + 1 + 1 + 1)) * t = 1 := OMA.Erdos724H1.two_inv j
  have cancel : ∀ a b : Fin (2 * j + 1 + 1 + 1), 2 * a = 2 * b → a = b := by
    intro a b hab
    calc a = (2 * t) * a := by rw [h2, one_mul]
      _ = t * (2 * a) := by ring
      _ = t * (2 * b) := by rw [hab]
      _ = (2 * t) * b := by ring
      _ = b := by rw [h2, one_mul]
  let L : LatinSquare (2 * j + 1 + 1 + 1) :=
    { mat := fun a b => a + b
      row_injective := fun a => add_right_injective a
      col_injective := fun b => by
        intro x y hxy
        change x + b = y + b at hxy
        simpa using hxy }
  let M : LatinSquare (2 * j + 1 + 1 + 1) :=
    { mat := fun a b => 2 * a + b
      row_injective := fun a => add_right_injective (2 * a)
      col_injective := fun b => by
        intro x y hxy
        change 2 * x + b = 2 * y + b at hxy
        apply cancel
        simpa using hxy }
  refine ⟨L, M, ?_, ?_⟩
  · intro hLM
    have h := congrArg (fun S : LatinSquare (2 * j + 1 + 1 + 1) => S.mat 1 0) hLM
    simp only [L, M, add_zero, mul_one] at h
    have hv := congrArg Fin.val h
    rw [Fin.val_one, Fin.val_two] at hv
    omega
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [L, M, Prod.mk.injEq] at h
    obtain ⟨h1, h2'⟩ := h
    have hac : a = c := by
      have : (2 * a + b) - (a + b) = (2 * c + d) - (c + d) := by rw [h1, h2']
      have e1 : (2 * a + b) - (a + b) = a := by ring
      have e2 : (2 * c + d) - (c + d) = c := by ring
      rw [e1, e2] at this
      exact this
    subst hac
    have hbd : b = d := by simpa using h1
    rw [hbd]
