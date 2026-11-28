import OMAStatements.S_oeis_a212797
import Mathlib

/-!
# Two recurrence identities for square triangular indices

Express twice the square triangular index using two consecutive terms of c.
Likewise, sixteen times g is a linear combination of those terms with coefficients affine in n.
The defining recurrences verify both expressions from their initial values.
Substitution then yields each of the claimed identities.
-/

namespace OMA.S_oeis_a212797

/-- The inhomogeneous recurrence differs from a combination of c terms by one. -/
lemma index_eq : ∀ n, 2*squareTriIndex n = c (n+1) - 3*c n - 1
  | 0 | 1 => by decide
  | n+2 => by
    rw [squareTriIndex]
    have h := index_eq n
    have h' := index_eq (n+1)
    simp only [c] at h' ⊢
    linarith

/-- The fourth-order recurrence admits an affine-coefficient expression in c. -/
lemma g_eq : ∀ n, 16*g n = (17*(n:ℤ)+16)*c (n+1) - (3*(n:ℤ)+3)*c n
  | 0 | 1 | 2 | 3 => by decide
  | n+4 => by
    rw [g]
    have h₀ := g_eq n
    have h₁ := g_eq (n+1)
    have h₂ := g_eq (n+2)
    have h₃ := g_eq (n+3)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, c] at h₁ h₂ h₃ ⊢
    linear_combination 12*h₃ - 38*h₂ + 12*h₁ - h₀

end OMA.S_oeis_a212797

open OMA.S_oeis_a212797 in
theorem OMA.solution : type_of% @OMA.S_oeis_a212797.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
    have hs := congrArg (fun z : ℤ => ((m:ℤ)+1)*z) (index_eq (m+1))
    have h₀ := g_eq m
    have h₁ := g_eq (m+1)
    simp only [a, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, c] at *
    nlinarith only [hs, h₀, h₁]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m+3 := ⟨n-3, by omega⟩
    have hs := congrArg (fun z : ℤ => ((m:ℤ)+3)*z) (index_eq (m+3))
    have h₀ := g_eq m
    have h₁ := g_eq (m+1)
    have h₂ := g_eq (m+2)
    simp only [show m+3-1 = m+2 by omega, show m+3-2 = m+1 by omega,
      Nat.add_sub_cancel, a, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, c] at *
    nlinarith only [hs, h₀, h₁, h₂]
