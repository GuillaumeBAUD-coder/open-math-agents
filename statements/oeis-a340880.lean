import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq

/-!
# OEIS A340880

Source: https://oeis.org/A340880
Credit: @NOELOO6

Peter Bala's February 2021 conjecture asks whether the row polynomial
values modulo every nonzero integer are eventually periodic, starting at
n = 1. The finite formula below is the one given in the Formula section
and Maple program, and gives the listed rows. The Comments normalize the
series with n(n+1)/2; the title instead prints k(k+1)/2.
-/

namespace OMA.S_oeis_a340880
open Finset

def R (q : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range n, (1+q)^(k*(k+1)/2)*∏ j ∈ Ico (k+1) n, ((1+q)^j-1)

theorem main : ∀ q N : ℤ, N≠0 →
    ∃ B P : ℕ, 0<B ∧ 0<P ∧ ∀ n≥B, R q (n+P) ≡ R q n [ZMOD N] := by
  sorry

end OMA.S_oeis_a340880
