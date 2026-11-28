import OMAStatements.S_mo_270672
import Mathlib

open Matrix

namespace OMA.S_mo_270672

def A0 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 0; 0, 0]

theorem aux : ¬ (∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod p)),
    IsOrthogonal A ∨ IsCompletelyNonOrthogonal A) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h 2 2 A0 with h1 | h1
  · have := h1.1
    have h2 := congrFun (congrFun this 1) 1
    revert h2
    decide
  · apply h1
    refine ⟨A0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h0
      have h2 := congrFun (congrFun h0 0) 0
      revert h2
      decide
    · decide
    · decide
    · decide
    · decide
    · decide

end OMA.S_mo_270672

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_270672.main) := OMA.S_mo_270672.aux
