import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H1: hypothesis H1 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1
-- Credit: @loremcdmx
-- H1 := ∀ n : ℕ, Odd n → 3 ≤ n → ∃ L M : LatinSquare n, L ≠ M ∧ IsOrthogonal L M  /-- Orders divisible by `4` have a pair of orthogonal Latin squares. -/

namespace OMA.Aux

open Erdos724
open Fin.CommRing

lemma two_mul_inv (n : ℕ) [NeZero n] (hn : Odd n) : ∃ h : Fin n, (2 : Fin n) * h = 1 := by
  obtain ⟨k, hk⟩ := hn
  refine ⟨((k + 1 : ℕ) : Fin n), ?_⟩
  have h2 : (2 : Fin n) * ((k + 1 : ℕ) : Fin n) = ((2 * (k + 1) : ℕ) : Fin n) := by
    push_cast; ring
  rw [h2]
  have : 2 * (k + 1) = n + 1 := by omega
  rw [this]
  push_cast
  simp

def sq (n : ℕ) [NeZero n] (c : Fin n) (hc : ∃ h : Fin n, c * h = 1) : LatinSquare n where
  mat := fun i j => i + c * j
  row_injective := by
    intro i a b hab
    obtain ⟨h, hh⟩ := hc
    have : c * a = c * b := add_left_cancel hab
    have h2 := congrArg (fun x => h * x) this
    have h2 : h * (c * a) = h * (c * b) := h2
    rw [← mul_assoc, ← mul_assoc, mul_comm h c, hh] at h2
    simpa using h2
  col_injective := by
    intro j a b hab
    have hab' : a + c * j = b + c * j := hab
    exact add_right_cancel hab'

end OMA.Aux

open Fin.CommRing

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1 := by
  intro n hn h3
  have : NeZero n := ⟨by omega⟩
  obtain ⟨h, hh⟩ := OMA.Aux.two_mul_inv n hn
  refine ⟨OMA.Aux.sq n 1 ⟨1, by simp⟩, OMA.Aux.sq n 2 ⟨h, hh⟩, ?_, ?_⟩
  · intro heq
    have := congrArg (fun L => L.mat 0 1) heq
    simp [OMA.Aux.sq] at this
    have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h10 : (1 : Fin n) = 0 := by linear_combination -this
    exact one_ne_zero h10
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hp
    simp only [OMA.Aux.sq, Prod.mk.injEq, one_mul] at hp
    obtain ⟨h1, h2⟩ := hp
    have hj : j = j' := by
      have : (i + 2 * j) - (i + j) = (i' + 2 * j') - (i' + j') := by rw [h1, h2]
      have e : ∀ a b : Fin n, (a + 2 * b) - (a + b) = b := fun a b => by ring
      rwa [e, e] at this
    subst hj
    have : i = i' := add_right_cancel h1
    rw [this]
