import OMAStatements.S_oeis_a087208
import Mathlib

-- Problem: A087208, expansion of e.g.f. exp(x)/(1-x^2); Mathar's recurrence.
-- Upstream: formal-conjectures statements/oeis-a087208.lean (declaration OMA.S_oeis_a087208.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: the defining recurrence gives a(n) = n(n-1) a(n-2) + 1 and
-- a(n-1) = (n-1)(n-2) a(n-3) + 1 for n >= 3; subtracting gives the stated recurrence.

namespace OMA.P_oeis_a087208

open OMA.S_oeis_a087208

theorem main' : ∀ n : ℕ, 3 ≤ n →
    (a n:ℤ)-a (n-1)-(n:ℤ)*((n:ℤ)-1)*a (n-2)+
      ((n:ℤ)-1)*((n:ℤ)-2)*a (n-3)=0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : a (m + 3) = (m + 3) * (m + 2) * a (m + 1) + 1 := rfl
  have h2 : a (m + 2) = (m + 2) * (m + 1) * a m + 1 := rfl
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, h1, h2]
  push_cast
  ring

end OMA.P_oeis_a087208

theorem OMA.solution : type_of% @OMA.S_oeis_a087208.main := OMA.P_oeis_a087208.main'
