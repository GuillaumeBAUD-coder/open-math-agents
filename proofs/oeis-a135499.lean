import OMAStatements.S_oeis_a135499
import Mathlib

-- Problem: oeis-a135499
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P135499
open OMA.S_oeis_a135499

lemma key (L : List ℕ) : ((Nat.ofDigits 10 L : ℕ) : ℤ) ≡ ((digitSums L).1 : ℤ) - (digitSums L).2 [ZMOD 11] := by
  induction L with
  | nil => simp [digitSums]
  | cons d l ih =>
    simp only [Nat.ofDigits_cons, digitSums]
    push_cast
    have : ((10 : ℤ) * (Nat.ofDigits 10 l : ℕ)) ≡ -(((digitSums l).1 : ℤ) - (digitSums l).2) [ZMOD 11] := by
      have h10 : (10 : ℤ) ≡ -1 [ZMOD 11] := by decide
      have := Int.ModEq.mul h10 ih
      simpa using this
    have := Int.ModEq.add (Int.ModEq.refl (d : ℤ)) this
    rw [show (d : ℤ) + -(((digitSums l).1 : ℤ) - (digitSums l).2) = (d : ℤ) + (digitSums l).2 - (digitSums l).1 by ring] at this
    simpa [Nat.coe_ofDigits] using this

theorem sol : type_of% @OMA.S_oeis_a135499.main := by
  rintro n ⟨-, h⟩
  have k := key (Nat.digits 10 n)
  rw [Nat.ofDigits_digits, h, sub_self] at k
  have : (11 : ℤ) ∣ (n : ℤ) := Int.ModEq.dvd k.symm |> fun h => by simpa using h
  exact_mod_cast this

end OMA.P135499

theorem OMA.solution : type_of% @OMA.S_oeis_a135499.main := OMA.P135499.sol
