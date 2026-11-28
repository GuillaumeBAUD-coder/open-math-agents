import Mathlib

/-!
# A direct transformation from the involution Hankel matrix to a Vandermonde matrix

Source: T. Amdeberhan, https://mathoverflow.net/questions/330082 (CC BY-SA 4.0).
Credit: @connoranderson.

The certificate retains the row and column operations. The two matrices reduce
to the same factorial diagonal by triangular matrices with all diagonal entries
one. The involution numbers use their standard recurrence.
-/

namespace OMA.S_mo_330082
open Matrix

def I : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n+2 => I (n+1)+(n+1)*I n

abbrev Mat (n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) ℚ

def lower {n : ℕ} (A : Mat n) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, i<j → A i j=0

def H (n : ℕ) : Mat n := fun i j => (I (i.val+j.val):ℚ)
def V (n : ℕ) : Mat n := fun i j => (i.val+1:ℚ)^j.val
def D (n : ℕ) : Mat n := diagonal (fun i => (i.val.factorial:ℚ))

theorem main : ∀ n : ℕ, ∃ L P C T : Mat n,
    lower L ∧ lower P ∧ lower C.transpose ∧ lower T.transpose ∧
    H n=L*D n*C ∧ V n*T=P*D n ∧ (H n).det=(V n).det := by
  sorry

end OMA.S_mo_330082
